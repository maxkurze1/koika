(*! C++ backend !*)
open Common
module Extr = Cuttlebone.Extr

let debug = false

(* #line pragmas make the C++ code harder to read, and they cover too-large a
   scope (in particular, the last #line pragma in a program overrides positions
   for all subsequent code, while we'd want to use the C++ positions for these
   lines) *)
let add_line_pragmas = false

(* The overhead of recording offsets and copying only the corresponding data
   seems too high to make the stack-based approach worthwhile, even when a rule
   touches many registers (copying the whole log at once is quite fast, while
   iterating through the list of modified registers is much slower, even when
   using explicit offsets into the structures rather than register names). *)
let use_dynamic_logs = false
let use_offsets_in_dynamic_log = false

type ('pos_t, 'var_t, 'fn_name_t, 'rule_name_t, 'reg_t, 'ext_fn_t) cpp_rule_t = {
    rl_external: bool;
    rl_name: 'rule_name_t;
    rl_reg_histories: 'reg_t -> Extr.register_history;
    rl_body: (('pos_t, 'reg_t) Extr.register_annotation,
              'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) Extr.rule;
  }

type ('pos_t, 'var_t, 'fn_name_t, 'rule_name_t, 'reg_t, 'ext_fn_t) cpp_input_t = {
    cpp_classname: string;
    cpp_module_name: string;

    cpp_pos_of_pos: 'pos_t -> Pos.t;
    cpp_var_names: 'var_t -> string;
    cpp_fn_names: 'fn_name_t -> string;
    cpp_rule_names: ?prefix:string -> 'rule_name_t -> string;

    cpp_scheduler: ('pos_t, 'rule_name_t) Extr.scheduler;
    cpp_rules: ('pos_t, 'var_t, 'fn_name_t, 'rule_name_t, 'reg_t, 'ext_fn_t) cpp_rule_t list;

    cpp_registers: 'reg_t array;
    cpp_register_sigs: 'reg_t -> reg_signature;
    cpp_register_kinds: 'reg_t -> Extr.register_kind;
    cpp_ext_sigs: 'ext_fn_t -> (ffi_signature * [`Function | `Method]);

    cpp_extfuns: string option;
  }

type cpp_output_t =
  { co_modname: string; co_hpp: Buffer.t; co_cpp: Buffer.t }

let sprintf = Printf.sprintf
let fprintf = Printf.fprintf

type program_info =
  { mutable pi_committed: bool;
    mutable pi_needs_multiprecision: bool;
    mutable pi_user_types: (string * typ) list;
    pi_ext_funcalls: (Common.ffi_signature, unit) Hashtbl.t }

let fresh_program_info () =
  { pi_committed = false;
    pi_needs_multiprecision = false;
    pi_user_types = [];
    pi_ext_funcalls = Hashtbl.create 50 }

let assert_uncommitted { pi_committed; _ } =
  assert (not pi_committed)

let request_multiprecision pi =
  assert_uncommitted pi;
  pi.pi_needs_multiprecision <- true

let register_type (pi: program_info) nm tau =
  match List.assoc_opt nm pi.pi_user_types with
  | Some tau' ->
     if tau <> tau' then
       failwith (sprintf "Incompatible uses of type name `%s':\n%s\n%s"
                   nm (typ_to_string tau) (typ_to_string tau'))
  | None ->
     assert_uncommitted pi;
     pi.pi_user_types <- (nm, tau) :: pi.pi_user_types

let gensym_prefix = "_"
let gensym, gensym_reset = make_gensym gensym_prefix
(* Mangling takes care of collisions with the gensym *)

module Mangling = struct
  let cpp_reserved =
    StringSet.of_list
      ["alignas"; "alignof"; "and"; "and_eq"; "asm"; "atomic_cancel";
       "atomic_commit"; "atomic_noexcept"; "auto"; "bitand"; "bitor"; "bool";
       "break"; "case"; "catch"; "char"; "char8_t"; "char16_t"; "char32_t";
       "class"; "compl"; "concept"; "const"; "consteval"; "constexpr";
       "constinit"; "const_cast"; "continue"; "co_await"; "co_return";
       "co_yield"; "decltype"; "default"; "delete"; "do"; "double";
       "dynamic_cast"; "else"; "enum"; "explicit"; "export"; "extern"; "false";
       "float"; "for"; "friend"; "goto"; "if"; "inline"; "int"; "long";
       "mutable"; "namespace"; "new"; "noexcept"; "not"; "not_eq"; "nullptr";
       "operator"; "or"; "or_eq"; "private"; "protected"; "public"; "reflexpr";
       "register"; "reinterpret_cast"; "requires"; "return"; "short"; "signed";
       "sizeof"; "static"; "static_assert"; "static_cast"; "struct"; "switch";
       "synchronized"; "template"; "this"; "thread_local"; "throw"; "true";
       "try"; "typedef"; "typeid"; "typename"; "union"; "unsigned"; "using";
       "virtual"; "void"; "volatile"; "wchar_t"; "while"; "xor"; "xor_eq"]
  let cuttlesim_reserved =
    StringSet.of_list
      ["array"; "unit"; "bits"]
  let reserved =
    StringSet.union cpp_reserved cuttlesim_reserved

  let mangling_prefix = "renamed_cpp"
  let specials_re = Str.regexp (sprintf "^\\(_[A-Z]\\|%s\\|%s\\)" mangling_prefix gensym_prefix)
  let dunder_re = Str.regexp "__+"
  let dunder_anchored_re = Str.regexp "^.*__"
  let dunder_target_re = Str.regexp "_\\(dx\\)\\([0-9]\\)_"
  let valid_name_re = Str.regexp "^[A-Za-z_][A-Za-z0-9_]*"

  let needs_mangling name =
    StringSet.mem name reserved
    || Str.string_match specials_re name 0
    || Str.string_match dunder_anchored_re name 0

  let escape_dunders name =
    let name = Str.global_replace dunder_target_re "_\\10\\2_" name in
    let subst _ = sprintf "_dx%d_" (Str.match_end () - Str.match_beginning ()) in
    Str.global_substitute dunder_re subst name

  let check_valid name =
    if not @@ Str.string_match valid_name_re name 0 then
      failwith (sprintf "Invalid name: `%s'" name)

  let add_prefix prefix name =
    if prefix = "" then name else prefix ^ "_" ^ name

  let mangle_name ?(prefix="") name =
    check_valid name;
    let unmangled = add_prefix prefix name in
    if needs_mangling unmangled then
      escape_dunders (add_prefix prefix (mangling_prefix ^ name))
    else unmangled

  let mangle_register_sig r =
    { r with reg_name = mangle_name r.reg_name }

  let mangle_function_sig (f, kind) =
    { f with ffi_name = mangle_name f.ffi_name }, kind

  let default v = function
    | Some v' -> v'
    | None -> v

  let mangle_unit u =
    { u with (* The prefixes are needed to prevent collisions with ‘prims::’ *)
      cpp_classname = mangle_name ~prefix:"module" u.cpp_classname;
      cpp_var_names = (fun v -> v |> u.cpp_var_names |> mangle_name);
      cpp_fn_names = (fun v -> v |> u.cpp_fn_names |> mangle_name);
      cpp_rule_names = (fun ?prefix rl ->
        rl |> u.cpp_rule_names |> mangle_name ~prefix:(default "rule" prefix));
      cpp_register_sigs = (fun r -> r |> u.cpp_register_sigs |> mangle_register_sig);
      cpp_ext_sigs = (fun f -> f |> u.cpp_ext_sigs |> mangle_function_sig) }
end

let cpp_enum_name pi sg =
  let name = Mangling.mangle_name ~prefix:"enum" sg.enum_name in
  register_type pi name (Enum_t sg); name

let cpp_struct_name pi sg =
  let name = Mangling.mangle_name ~prefix:"struct" sg.struct_name in
  register_type pi sg.struct_name (Struct_t sg); name

let cpp_type_of_size
      (pi: program_info)
      (stem: string) (sz: int) =
  assert (sz >= 0);
  if sz > 64 then
    request_multiprecision pi;
  if sz = 0 then
    "unit"
  else if sz <= 1024 then
    sprintf "%s<%d>" stem sz
  else
    failwith (sprintf "Unsupported size: %d" sz)

let cpp_value_type_of_size
      (pi: program_info)
      (sz: int) =
  cpp_type_of_size pi "bits_t" sz

let rec cpp_type_of_type
          (pi: program_info)
          (tau: typ) =
  match tau with
  | Bits_t sz -> cpp_type_of_size pi "bits" sz
  | Enum_t sg -> cpp_enum_name pi sg
  | Struct_t sg -> cpp_struct_name pi sg
  | Array_t sg -> cpp_type_of_array pi sg
and cpp_type_of_array pi { array_type; array_len } =
  sprintf "array<%s, %d>"
    (cpp_type_of_type pi array_type) array_len

let cpp_enumerator_name pi ?(enum=None) nm =
  let nm = Mangling.mangle_name nm in
  match enum with
  | None -> nm
  | Some sg -> sprintf "%s::%s" (cpp_enum_name pi sg) nm

let cpp_field_name nm =
  Mangling.mangle_name nm

let register_subtypes (pi: program_info) tau =
  let rec loop tau = match tau with
    | Bits_t sz -> if sz > 64 then request_multiprecision pi
    | Enum_t sg -> ignore (cpp_enum_name pi sg)
    | Struct_t sg -> ignore (cpp_struct_name pi sg);
                     List.iter (loop << snd) sg.struct_fields
    | Array_t { array_type; _ } -> loop array_type in
  loop tau

let z_to_str (base: [`Bin | `Hex]) bitlen z =
  let b, w = match base with
    | `Hex -> "x", (bitlen + 7) / 8
    | `Bin -> "b", bitlen in
  let fmt = sprintf "%%0%d%s" w b in
  Z.format fmt z

let cpp_const_init (pi: program_info) immediate sz cst =
  assert (sz >= 0);
  if sz > 64 then
    request_multiprecision pi;
  if sz = 0 then
    if immediate then "prims::tt.v" else "prims::tt"
  else
    let imm_suffix = if immediate then "v" else "" in
    let wide = sz > 8 in
    let trivial = Z.equal cst Z.zero || Z.equal cst Z.one in
    let bitlen = if wide && trivial then 0 else sz in
    if bitlen <= 8 && sz <= 64 then
      let lit = z_to_str `Bin bitlen cst in
      let prefix = sprintf "%d'" sz in
      prefix ^ lit ^ "_b" ^ imm_suffix
    else if sz <= 1024 then
      let lit = z_to_str `Hex bitlen cst in
      let prefix = sprintf "0x%d'" sz in
      prefix ^ lit ^ "_x" ^ imm_suffix
    else
      failwith (sprintf "Unsupported size: %d" sz)

let cpp_type_needs_allocation _tau =
  false (* boost::multiprecision has literals *)

let assert_bits (tau: typ) =
  match tau with
  | Bits_t sz -> sz
  | _ -> failwith "Expecting bits, not struct or enum"

let cpp_ext_funcall f (kind: [`Function | `Method]) a =
  (* The current implementation of external functions requires the client to
     pass a class implementing those functions as a template argument.  An
     other approach would have made external functions virtual methods, but
     then they couldn't have been templated functions. *)
  (* Originally, the call was written as ‘extfuns.template %s()’to ensure that
     ‘extfuns.xyz<p>()’ would not parsed as a comparison, but clang rejects this
     for non-templated functions in version 10.  Users will have to declare
     their function names to be ‘template xyz<p>’ instead of ‘xyz<p>’ *)
  sprintf "extfuns.%s(%s%s)" f (if kind = `Method then "*this, " else "") a

let cpp_bits1_fn_name (f: Extr.PrimTyped.fbits1) =
  match f with
  | Not _ -> "~"
  | SExt (_sz, width) -> sprintf "prims::sext<%d>" width
  | ZExtL (_sz, width) -> sprintf "prims::zextl<%d>" width
  | ZExtR (_sz, width) -> sprintf "prims::zextr<%d>" width
  | Repeat (_sz, times) -> sprintf "prims::repeat<%d>" times
  | Slice (_sz, offset, width) -> sprintf "prims::slice<%d, %d>" offset width
  | Lowered (IgnoreBits _sz) -> "prims::ignore"
  | Lowered (DisplayBits _) -> failwith "Do not use DisplayBits; use Display with Unpack instead"

let cpp_bits2_fn_name (f: Extr.PrimTyped.fbits2) =
  match f with
  | And _ -> `Infix "&"
  | Or _ -> `Infix "|"
  | Xor _ -> `Infix "^"
  | Lsl _ -> `Infix "<<"
  | Lsr _ -> `Infix ">>"
  | Asr _ -> `Fn "prims::asr"
  | Concat _ -> `Fn "prims::concat"
  | Sel _ -> `Array
  | SliceSubst (_sz, offset, _width) -> `Fn (sprintf "prims::slice_subst<%d>" offset)
  | IndexedSlice (_sz, width) -> `Fn (sprintf "prims::islice<%d>" width)
  | Plus _ -> `Infix "+"
  | Minus _ -> `Infix "-"
  | Mul _ -> `Infix "*"
  | EqBits (_, true) -> `Infix "!="
  | EqBits (_, false) -> `Infix "=="
  | Compare (true, cmp, _) ->
     `Fn (match cmp with CLt -> "slt" | CGt -> "sgt" | CLe -> "sle" | CGe -> "sge")
  | Compare (false, cmp, _) ->
     `Infix (match cmp with CLt -> "<" | CGt -> ">" | CLe -> "<=" | CGe -> ">=")

let cuttlesim_hpp =
  (* resources.ml is auto-generated *)
  Resources.cuttlesim_hpp

let cuttlesim_hpp_fname =
  "cuttlesim.hpp"

let reconstruct_switch action =
  let rec loop v = function
    | Extr.If (_, _,
               Extr.Binop (_,
                           (Extr.PrimTyped.Eq (_, false) |
                              Extr.PrimTyped.Bits2 (Extr.PrimTyped.EqBits (_, false))),
                           Extr.Var (_, v', ((Extr.Bits_t _ | Extr.Enum_t _) as tau), _m),
                           value),
               tbr, fbr) when (match v with Some v -> v' = v | None -> true) ->
       (match Cuttlebone.Util.interp_arithmetic value with
        | None -> None
        | Some cst ->
           let default, branches = match loop (Some v') fbr with
             | Some (_, _, default, branches) -> default, branches
             | None -> fbr, [] in
           Some (v', tau, default, (cst, tbr) :: branches))
    | _ -> None in
  match loop None action with
  | Some (_, _, _, [_]) | None -> None
  | res -> res

type target_info =
  { tau: typ; mutable declared: bool; name: var_t }

type assignment_target =
  | NoTarget
  | VarTarget of target_info

type assignment_result =
  | NotAssigned
  | Assigned of var_t
  | PureExpr of string
  | ImpureExpr of string

let assignment_result_to_string (d: assignment_result) =
  match d with
  | NotAssigned -> sprintf "NotAssigned"
  | Assigned v -> sprintf "Assigned %s" v
  | PureExpr s -> sprintf "PureExpr %s" s
  | ImpureExpr s -> sprintf "ImpureExpr %s" s

let compile (type pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t)
      (hpp: (pos_t, var_t, fn_name_t, rule_name_t, reg_t, ext_fn_t) cpp_input_t) =
  let buffer = ref (Buffer.create 0) in
  let hpp = Mangling.mangle_unit hpp in

  let nl _ = Buffer.add_string !buffer "\n" in
  let pk k fmt = Printf.kbprintf k !buffer fmt in
  let p fmt = pk nl fmt in
  let pr fmt = pk ignore fmt in
  let p_buffer b = Buffer.add_buffer !buffer b in
  let set_buffer b = let b' = !buffer in buffer := b; b' in

  let program_info = fresh_program_info () in
  let cpp_type_of_type = cpp_type_of_type program_info in
  let cpp_type_of_array = cpp_type_of_array program_info in
  let cpp_value_type_of_size = cpp_value_type_of_size program_info in
  let cpp_enum_name = cpp_enum_name program_info in
  let cpp_struct_name = cpp_struct_name program_info in
  let cpp_enumerator_name = cpp_enumerator_name program_info in
  let cpp_const_init = cpp_const_init program_info in

  let reg_list =
    Array.to_list hpp.cpp_registers in
  let may_fail_fast =
    Cuttlebone.Util.may_fail_without_revert reg_list in
  let needs_data0_and_data1 =
    Cuttlebone.Util.need_data0_and_data1 reg_list in

  let rec iter_sep sep body = function
    | [] -> ()
    | item :: [] -> body item
    | item :: items -> body item; sep (); iter_sep sep body items in

  let p_comment fmt =
    pr "/* "; pk (fun _ -> pr " */"; nl ()) fmt in

  let p_ifdef condition pbody =
    p "#if%s" condition;
    pbody ();
    p "#endif" in

  let p_ifnminimal pbody =
    p_ifdef "ndef SIM_MINIMAL" pbody in

  let p_scoped header ?(terminator="") pbody =
    p "%s {" header;
    let r = pbody () in
    p "}%s" terminator;
    r in

  let p_fn ~typ ~name ?(args="") ?(annot="") pbody =
    p_scoped (sprintf "%s %s(%s)%s" typ name args annot) pbody in

  let p_includeguard pbody =
    let cpp_define = sprintf "%s_HPP" (String.uppercase_ascii hpp.cpp_classname) in
    p "#ifndef %s" cpp_define;
    p "#define %s" cpp_define;
    nl ();
    pbody ();
    p "#endif" in

  let p_cpp_decl ?(prefix = "") ?init typ name =
    pr "%s" prefix;
    match init with
    | None -> p "%s %s;" typ name
    | Some init -> p "%s %s = %s;" typ name init in

  let p_decl ?(prefix = "") ?init tau name =
    p_cpp_decl ~prefix ?init (cpp_type_of_type tau) name in

  let bits_to_Z bits =
    Z.(Array.fold_right (fun b z ->
           (if b then one else zero) + shift_left z 1)
         bits zero) in

  let rec sp_value ?(immediate=false) (v: value) =
    match v with
    | Bits bs -> sp_bits_value ~immediate bs
    | Enum (sg, v) -> sp_enum_value sg v
    | Struct (sg, fields) -> sp_struct_value sg fields
    | Array (tau, values) -> sp_array_value tau values
  and sp_bits_value ?(immediate=false) bs =
    let z = bits_to_Z bs in
    let bitlength = Array.length bs in
    cpp_const_init immediate bitlength z
  and sp_enum_value sg v =
    match enum_find_field_opt sg v with
    | None -> sprintf "static_cast<%s>(%s.v)" (cpp_enum_name sg) (sp_bits_value v)
    | Some nm -> cpp_enumerator_name ~enum:(Some sg) nm
  and sp_struct_value sg fields =
    let fields = String.concat ", " (List.map sp_value fields) in
    sprintf "%s{ %s }" (cpp_struct_name sg) fields
  and sp_array_value sg values =
    let vals = String.concat ", " (List.map sp_value (Array.to_list values)) in
    sprintf "%s{%s}" (cpp_type_of_array sg) vals
  in

  let sp_binop op a1 a2 =
    match op with
    | `Infix op -> sprintf "(%s %s %s)" a1 op a2
    | `Fn f -> sprintf "%s(%s, %s)" f a1 a2
    | `Array -> sprintf "%s[%s]" a1 a2 in

  let sp_equality ?(negated=false) a1 a2 =
    sp_binop (`Infix (if negated then "!=" else "==")) a1 a2 in

  let sp_initializer tau =
    (* This is needed for readability rather than performance, since GCC is
       smart enough to optimize unpack(0). *)
    sprintf "%s{}" (cpp_type_of_type tau) in

  let sp_parenthesized arg =
    if arg = "" then "" else sprintf "(%s)" arg in

  let sp_packer ?(arg = "") tau =
    let parg = sp_parenthesized arg in
    match tau with
    | Bits_t _ -> arg
    | Enum_t _ | Struct_t _ | Array_t _ -> sprintf "prims::pack%s" parg in

  let sp_unpacker ?(arg = "") tau =
    let parg = sp_parenthesized arg in
    match tau with
    | Bits_t _ -> arg
    | Enum_t sg ->
       sprintf "prims::unpack<%s>%s" (cpp_enum_name sg) parg
    | Struct_t sg ->
       sprintf "prims::unpack<%s>%s" (cpp_struct_name sg) parg
    | Array_t sg ->
       sprintf "prims::unpack<%s>%s" (cpp_type_of_array sg) parg in

  let p_enum_decl sg =
    let esz = enum_sz sg in
    let nm = cpp_enum_name sg in
    if esz = 0 then failwith (sprintf "Enum %s is empty (its members are zero-bits wide)" nm);
    if esz > 64 then failwith (sprintf "Enum %s is too large (its members are %d-bits wide; the limit is 64)" nm esz);
    let decl = sprintf "enum class %s : %s" nm (cpp_value_type_of_size esz) in
    p_scoped decl ~terminator:";" (fun () ->
        iter_sep (fun () -> p ", ")
          (fun (name, v) ->
            let nm = cpp_enumerator_name name in
            let vstr = sp_bits_value ~immediate:true v in
            p "%s = %s" nm vstr)
          sg.enum_members) in

  let p_struct_decl sg =
    let decl = sprintf "struct %s" (cpp_struct_name sg) in
    p_scoped decl ~terminator:";" (fun () ->
        List.iter (fun (name, tau) -> p_decl tau (cpp_field_name name)) sg.struct_fields) in

  let p_printer tau =
    let v_arg = "val" in
    let v_tau = cpp_type_of_type tau in
    let v_style = "const fmtopts opts" in
    let v_argdecl = sprintf "std::ostream& os, const %s& %s" v_tau v_arg in

    let p_printer pbody =
      p_fn ~typ:"static _unused std::ostream&" ~name:"fmt"
        ~args:(sprintf "%s, %s" v_argdecl v_style) (fun () ->
          pbody (); p "return os;") in

    let p_enum_printer sg =
      p_printer (fun () ->
          p_scoped (sprintf "switch (%s)" v_arg) (fun () ->
              List.iter (fun (nm, _v) ->
                  let lbl = cpp_enumerator_name ~enum:(Some sg) nm in
                  p "case %s: os << \"%s::%s\"; break;" lbl sg.enum_name nm) (* unmangled *)
                sg.enum_members;
              let v_sz = typ_sz tau in
              let bits_sz_tau = cpp_type_of_type (Bits_t v_sz) in
              let v_cast = sprintf "%s::mk(%s)" bits_sz_tau v_arg in
              p "default: os << \"%s{\"; fmt(os, %s, opts) << \"}\";"
                sg.enum_name v_cast)) in (* unmangled *)

    let p_struct_printer sg =
      p_printer (fun () ->
          p "os << \"%s { \";" sg.struct_name; (* unmangled *)
          List.iter (fun (fname, _) ->
              p "os << \".%s = \"; fmt(os, %s.%s, opts) << \"; \";" (* unmangled *)
                fname v_arg (cpp_field_name fname))
            sg.struct_fields;
          p "os << \"}\";") in

    match tau with
    | Bits_t _ | Array_t _ -> ()
    | Enum_t sg -> p_enum_printer sg
    | Struct_t sg -> p_struct_printer sg in

  let p_operators tau =
    let v_sz = typ_sz tau in
    let v1, v2 = "v1", "v2" in
    let v_tau = cpp_type_of_type tau in
    let v_argdecl v = sprintf "const %s %s" v_tau v in
    let bits_tau = cpp_type_of_type (Bits_t v_sz) in

    let p_ostream_printer () =
      let args = sprintf "std::ostream& os, const %s& val" v_tau in
      p_fn ~typ:"static _unused std::ostream&" ~name:"operator<<" ~args
        (fun () -> p "return prims::fmt(os, val);") in

    let p_eq prbody =
      p_fn ~typ:"static _unused bits<1> "
        ~args:(sprintf "%s, %s" (v_argdecl v1) (v_argdecl v2))
        ~name:"operator==" (fun () -> pr "return "; prbody (); p ";");
      p_fn ~typ:"static _unused bits<1> "
        ~args:(sprintf "%s, %s" (v_argdecl v1) (v_argdecl v2))
        ~name:"operator!=" (fun () -> pr "return !(%s == %s);" v1 v2)in

    let p_enum_eq _sg =
      p_eq (fun () -> pr "%s::mk(%s) == %s::mk(%s)" bits_tau v1 bits_tau v2) in

    let sp_field_eq v1 v2 field =
      let field = cpp_field_name field in
      let eq = sp_equality (v1 ^ "." ^ field) (v2 ^ "." ^ field) in
      sprintf "bool%s" eq in

    let p_struct_eq sg =
      p_eq (fun () ->
          pr "bits<1>::mk(";
          iter_sep (fun () -> pr " && ") (fun (nm, _) ->
              pr "%s" (sp_field_eq v1 v2 nm))
            sg.struct_fields;
          pr ")") in

    (match tau with
     | Bits_t _ | Array_t _ -> ()
     | Enum_t sg -> p_enum_eq sg
     | Struct_t sg -> p_struct_eq sg);
    nl ();
    p_ifnminimal (fun () ->
        p_ostream_printer ()) in

  let p_prims tau =
    let v_sz = typ_sz tau in
    let v_arg = "val" in
    let v_tau = cpp_type_of_type tau in
    let v_argdecl v = sprintf "const %s %s" v_tau v in
    let bits_arg = "bs" in
    let bits_tau = cpp_type_of_type (Bits_t v_sz) in
    let bits_argdecl = sprintf "const %s %s" bits_tau bits_arg in

    let p_pack pbody =
      p_fn ~typ:("template <> _unused " ^ bits_tau)
        ~args:(v_argdecl v_arg) ~name:"pack<>" pbody in

    let p_unpack pbody =
      let decl = sprintf "template <> struct _unpack<%s, %d>" v_tau v_sz in
      p_scoped decl ~terminator:";" (fun () ->
          p_fn ~typ:("static " ^ v_tau)
            ~args:bits_argdecl ~name:"unpack" pbody) in

    let p_enum_pack _ =
      p_pack (fun () -> p "return %s::mk(%s);" bits_tau v_arg) in

    let p_enum_unpack _ =
      p_unpack (fun () -> p "return static_cast<%s>(%s.v);" v_tau bits_arg) in

    let p_struct_pack sg =
      let var = "packed" in
      p_pack (fun () ->
          p_decl (Bits_t v_sz) var ~init:(cpp_const_init false v_sz Z.zero);
          List.iteri (fun idx (fname, ftau) ->
              let sz = typ_sz ftau in
              let fname = cpp_field_name fname in
              let fval = sprintf "%s.%s" v_arg fname in
              let fpacked = sp_packer ftau ~arg:fval in
              if idx <> 0 then p "%s <<= %d;" var sz;
              p "%s |= prims::widen<%d>(%s);" var v_sz fpacked)
            sg.struct_fields;
          p "return %s;" var) in

    let p_struct_unpack sg =
      let var = "unpacked" in
      p_unpack (fun () ->
          p_decl tau var ~init:"{}";
          List.fold_right (fun (fname, ftau) offset ->
              let sz = typ_sz ftau in
              let fname = cpp_field_name fname in
              let fval = sprintf "prims::truncate<%d>(%s >> %du)"
                           sz bits_arg offset in
              let unpacked = sp_unpacker ~arg:fval ftau in
              p "%s.%s = %s;" var fname unpacked;
              offset + sz)
            sg.struct_fields 0 |> ignore;
          p "return %s;" var) in

    let p_type_info () =
      let decl = sprintf "template <> struct type_info<%s>" v_tau in
      p_scoped decl ~terminator:";" (fun () ->
          p_cpp_decl ~prefix:"static constexpr " ~init:(sprintf "%d" v_sz)
            "prims::bitwidth" "size") in

    p_type_info ();
    nl ();
    match tau with
    | Bits_t _ | Array_t _ -> ()
    | Enum_t sg -> p_enum_pack sg; nl (); p_enum_unpack sg
    | Struct_t sg -> p_struct_pack sg; nl (); p_struct_unpack sg in

  let complete_user_types () =
    let reg_typ (_, t) = register_subtypes program_info t in
    List.iter reg_typ program_info.pi_user_types;
    program_info.pi_user_types in

  let p_type_declarations () =
    p "//////////////";
    p "// TYPEDEFS //";
    p "//////////////";
    nl ();
    let types = complete_user_types () in
    let types = topo_sort_types (sort_types (List.map snd types)) in
    let enums, structs = partition_types types in
    List.iter p_enum_decl enums;
    nl ();
    iter_sep nl p_struct_decl structs;
    nl ();
    iter_sep nl p_operators types;
    nl ();
    p_scoped "namespace prims" (fun () ->
        p_ifnminimal (fun () ->
            iter_sep nl p_printer types);
        nl ();
        iter_sep nl p_prims types) in

  let p_preamble () =
    p "//////////////";
    p "// PREAMBLE //";
    p "//////////////";
    nl ();
    program_info.pi_committed <- true;
    if program_info.pi_needs_multiprecision then (
      p "#define NEEDS_BOOST_MULTIPRECISION";
      nl ());
    p "#include \"%s\"" cuttlesim_hpp_fname in

  let iter_registers f regs =
    let sigs = Array.map hpp.cpp_register_sigs regs in
    Array.iter f sigs in

  let all_register_sigs =
    Array.map hpp.cpp_register_sigs hpp.cpp_registers in

  let iter_all_registers f =
    Array.iter f all_register_sigs in

  let reg_sig_w_kind r =
    (hpp.cpp_register_kinds r, hpp.cpp_register_sigs r) in

  let iter_all_registers_with_kind =
    let sigs = Array.map reg_sig_w_kind hpp.cpp_registers in
    fun f -> Array.iter f sigs in

  let p_impl () =
    p "////////////////////";
    p "// IMPLEMENTATION //";
    p "////////////////////";
    nl ();

    let p_sim_class pbody =
      p_scoped (sprintf "template <typename extfuns_t> class %s" hpp.cpp_classname)
        ~terminator:";" pbody in

    let p_state_register r =
      p_decl (reg_type r) r.reg_name in

    let p_state_methods () =
      let p_dump_register r =
        p "os << \"%s = \" << %s << std::endl;"
          r.reg_name r.reg_name in
      let p_dump () =
        p_fn ~typ:"void" ~name:"dump" ~annot:" const"
          ~args:"std::ostream& os = std::cout"
          (fun () -> iter_all_registers p_dump_register) in

      let p_vcd_decl r =
        p "cuttlesim::vcd::var(os, \"%s\", %d);"
          r.reg_name (typ_sz (reg_type r)) in
      let p_vcd_header () =
        p_fn ~typ:"static _unused void" ~name:"vcd_header"
          ~args:"std::ostream& os" (fun () ->
            p_ifdef "ndef SIM_VCD_SCOPES" (fun () ->
                p "#define SIM_VCD_SCOPES { \"TOP\", \"%s\" }" hpp.cpp_module_name);
            p "cuttlesim::vcd::begin_header(os, SIM_VCD_SCOPES);";
            iter_all_registers p_vcd_decl;
            p "cuttlesim::vcd::end_header(os, SIM_VCD_SCOPES);") in

      let p_dumpvar r =
        p "cuttlesim::vcd::dumpvar(os, \"%s\", %s, previous.%s, force);"
          r.reg_name r.reg_name r.reg_name in
      let p_vcd_dumpvars () =
        p_fn ~typ:"void" ~name:"vcd_dumpvars"
          ~args:(sprintf "%s, %s, %s, %s"
                   "std::uint_fast64_t cycle_id"
                   "_unused std::ostream& os"
                   "const state_t& previous"
                   "const bool force")
          ~annot:" const" (fun () ->
            p "os << '#' << cycle_id << std::endl;";
            iter_all_registers p_dumpvar) in

      let p_readvar i r =
        let hdr = if i == 0 then "if" else "else if" in
        p_scoped (sprintf "%s (var == \"%s\")" hdr r.reg_name) (fun () ->
            let tau = reg_type r in
            p "%s = prims::unpack<%s>(bits<%d>::of_str(val));"
              r.reg_name (cpp_type_of_type tau) (typ_sz tau)) in
      let p_vcd_readvars () =
        p_fn ~typ:"std::uint_fast64_t" ~name:"vcd_readvars"
          ~args:"_unused std::istream& is" (fun () ->
            p "std::string var{}, val{};";
            p "std::uint_fast64_t cycle_id = std::numeric_limits<std::uint_fast64_t>::max();";
            p "cuttlesim::vcd::read_header(is);";
            p_scoped "while (cuttlesim::vcd::readvar(is, cycle_id, var, val))" (fun () ->
                Array.iteri p_readvar all_register_sigs);
            p "return cycle_id;") in

      p_ifnminimal (fun () ->
          p_dump ();
          nl ();
          p_vcd_header ();
          nl ();
          p_vcd_dumpvars ();
          nl ();
          p_vcd_readvars ()) in

    let p_state_t () =
      p_scoped "struct state_t" ~terminator:";" (fun () ->
          iter_all_registers p_state_register;
          nl ();
          p_state_methods ()) in

    let p_snapshot_t () =
      p "using snapshot_t = cuttlesim::snapshot_t<state_t>;" in

    let p_reg_name_t () =
      let p_decl_rwset_register r =
        p "%s," r.reg_name in
      let name_sz =
        (* Compute the smallest bitwidth that can fit all names *)
        Cuttlebone.Util.log2 (1 + Array.length hpp.cpp_registers) in
      p_scoped (sprintf "enum class reg_name_t : bits_t<%d>" name_sz)
        ~terminator:";" (fun () ->
          p "_invalid = 0,";
          iter_all_registers p_decl_rwset_register) in

    let p_dynamic_log_t () =
      if not use_offsets_in_dynamic_log then
        (p_reg_name_t ();
         nl ());
      let dynlog_type =
        if use_offsets_in_dynamic_log
        then "cuttlesim::offsets" else "reg_name_t" in
      let decl =
        sprintf "%s struct dynamic_log_t : %s"
          "template<int capacity>"
          (sprintf "cuttlesim::stack<%s, capacity>" dynlog_type) in
      p_scoped decl ~terminator:";" (fun () ->
          p_fn ~typ:"void" ~name:"apply" ~args:"log_t& dst, log_t& src"
            (fun () ->
              (* Unrolling this loop by copying everything up to capacity
                 doesn't help.  Nor does it help to get rid of the switch by
                 recording struct offsets instead of register names into the
                 dynamic log. *)
              p_scoped "for (int idx = 0; idx < this->sz; idx++)" (fun  () ->
                  if use_offsets_in_dynamic_log then
                    let ri ptr = sprintf "reinterpret_cast<char*>(%s)" ptr in
                    p "this->data[idx].memcpy(%s, %s, %s, %s);"
                      (ri "&dst.state") (ri "&src.state")
                      (ri "&dst.rwset") (ri "&src.rwset")
                  else
                    p_scoped "switch (this->data[idx])" (fun () ->
                        let p_apply_one r =
                          p "case reg_name_t::%s:" r.reg_name;
                          p "dst.state.%s = src.state.%s;" r.reg_name r.reg_name;
                          p "dst.rwset.%s = src.rwset.%s;" r.reg_name r.reg_name;
                          p "break;" in
                        iter_all_registers p_apply_one)))) in

    let p_rwset_t () =
      let rwset_type_of_kind = function
        | Extr.Value -> None
        | Extr.Wire -> Some "wire_rwset"
        | Extr.Register -> Some "reg_rwset"
        | Extr.EHR -> Some "ehr_rwset" in
      let p_decl_rwset_register (kd, r) =
        match rwset_type_of_kind kd with
        | None -> ()
        | Some rwset -> p "cuttlesim::%s %s;" rwset r.reg_name in
      p_scoped "struct rwset_t" ~terminator:";" (fun () ->
          iter_all_registers_with_kind p_decl_rwset_register) in

    let p_log_t () =
      p_scoped "struct log_t" ~terminator:";" (fun () ->
          p "rwset_t rwset;";
          p "state_t state;";
          nl ();
          p_fn ~typ:"const state_t&" ~name:"snapshot" ~annot:" const" (fun () ->
              p "return state;");
          p_fn ~typ:"explicit" ~name:"log_t" ~args:"const state_t& init"
            ~annot:" : rwset{}, state(init)" (fun () -> ())) in

    let backslash_re =
      Str.regexp "\\\\" in

    let sp_escaped_string s =
      Str.global_replace backslash_re "\\\\\\\\" s in

    let p_pos (pos: Pos.t) =
      if add_line_pragmas then
        match pos with
        | Unknown | StrPos _ | Filename _ -> ()
        | Range (filename, { rbeg = { line; _ }; _ }) ->
           p "#line %d \"%s\"" line (sp_escaped_string filename) in

    (* Map used to avoid collisions between function names *)
    let internal_fnames = Hashtbl.create 20 in

    let p_rule (rule: (pos_t, var_t, fn_name_t, rule_name_t, reg_t, ext_fn_t) cpp_rule_t) =
      gensym_reset ();

      let filter_registers_by_history cond =
        List.filter (fun reg -> cond reg (rule.rl_reg_histories reg))
          (Array.to_list hpp.cpp_registers)
        |> Array.of_list in

      (* Check for registers that would require keeping track of data0 and data1
         separately, and issue a warning if there are any. *)
      let _ =
        match needs_data0_and_data1  rule.rl_body with
        | [] -> ()
        | conflicts ->
           let names = List.map (fun r -> (hpp.cpp_register_sigs r).reg_name) conflicts |> String.concat ", " in
           Printf.eprintf "Warning: Rule %s reads registers [%s] at port 1 \
after writing to them at port 1.
These reads should observe the old value of the registers, but \
implementing this in simulation causes unnecessary performance issues.
If you actually want to observe the old values, use let bindings to save \
them before writing to the registers.\n"
             (hpp.cpp_rule_names rule.rl_name)
             names in

      let rwset_footprint =
        (* No need to save or reset a register's read-write set if it's only
           read at port 0, or if it's a value (i.e. a register for which reads
           and writes cannot fail in any rule, in which case we don't generate a
           read-write set at all). *)
        filter_registers_by_history (fun reg { hr1; hw0; hw1; _ } ->
            hpp.cpp_register_kinds reg <> Value &&
            Extr.(hr1 <> TFalse || hw0 <> TFalse || hw1 <> TFalse)) in

      let rwdata_footprint =
        (* No need to save or reset a register's data if it's only read *)
        filter_registers_by_history (fun _reg { hw0; hw1; _ } ->
            Extr.(hw0 <> TFalse || hw1 <> TFalse)) in

      if debug then (
        let debug_footprint name fp =
          Printf.printf "Footprints for %s in %s:\n"
            name (hpp.cpp_rule_names rule.rl_name);
          Array.iter (fun r ->
              let nm = (hpp.cpp_register_sigs r).reg_name in
              let rfp = rule.rl_reg_histories r in
              let pr = function
                | Extr.TTrue -> "true"
                | Extr.TFalse -> "false"
                | Extr.TUnknown -> "?" in
              Printf.printf "  %s: {r0=%s; r1=%s; w0=%s; w1=%s; cf=%s}\n" nm
                (pr rfp.hr0) (pr rfp.hr1) (pr rfp.hw0) (pr rfp.hw1) (pr rfp.hcf))
            fp in

        debug_footprint "rwset" rwset_footprint;
        debug_footprint "rwdata" rwdata_footprint);

      let large_footprint footprint = (* FIXME should be tweaked based on the speed of memset *)
        5 * Array.length footprint > 4 * Array.length hpp.cpp_registers in

      let rule_max_log_size =
        Extr.rule_max_log_size rule.rl_body in

      let use_dynamic_log =
        (* LATER: Refine this criterion based on rule_max_log_size; at the moment
           this measure isn't precise enough to be truly useful, because it
           overestimates log sizes in imperative switches. *)
        use_dynamic_logs && (Array.length rwdata_footprint > 10 ||
                               Array.length rwset_footprint > 10) in

      let dl_suffix =
        if use_dynamic_log
        then (if use_offsets_in_dynamic_log then "_DOL" else "_DL")
        else "" in
      let fail safe = sprintf "FAIL%s" (if safe then "_FAST" else dl_suffix) in
      let commit = sprintf "COMMIT%s" dl_suffix in
      let call = sprintf "CALL_FN" in
      let rw_suffix reg =
        if hpp.cpp_register_kinds reg = Value then "_FAST" else dl_suffix in
      let read reg pt =
        sprintf "READ%d%s" pt (rw_suffix reg) in
      let write reg pt = sprintf "WRITE%d%s" pt (rw_suffix reg) in

      let p_copy field src dst footprint =
        let src = sprintf "%s.%s" src field in
        let dst = sprintf "%s.%s" dst field in
        if large_footprint footprint then
          p "%s = %s;" dst src
        else
          iter_registers (fun { reg_name; _ } ->
              p "%s.%s = %s.%s;" dst reg_name src reg_name)
            footprint in

      let p_commit_reset src dst =
        if large_footprint rwdata_footprint &&
             large_footprint rwset_footprint then
          p "%s = %s;" dst src
        else (
          p_copy "state" src dst rwdata_footprint;
          p_copy "rwset" src dst rwset_footprint) in

      let p_reset () = p_commit_reset "Log" "log" in
      let p_commit () = p_commit_reset "log" "Log" in

      let p_declare_target = function
        | VarTarget ({ tau; declared = false; name } as ti) ->
           p_decl tau name;
           ti.declared <- true
        | _ -> () in

      let gensym_target_info tau prefix =
        { tau; declared = false; name = gensym prefix } in

      let gensym_target tau prefix =
        VarTarget (gensym_target_info tau prefix) in

      let maybe_gensym_target existing_target tau0 prefix =
        (* Return ‘existing_target’ if it can store a value of type ‘tau0’;
           otherwise, gensym a target starting with ‘prefix’.  This allows us to
           print ‘subst(y, f, 1)’ with target ‘x’ as ‘x = y; x.f = 1’ instead of
           ‘tmp = y; x = tmp; x.f = 1’. *)
        match existing_target with
        | VarTarget { tau; _ } when tau = tau0 -> existing_target
        | VarTarget _ | NoTarget -> gensym_target tau0 prefix in

      let ensure_target tau t =
        match t with
        | NoTarget -> gensym_target_info tau "ignored"
        | VarTarget info -> info in

      let p_assign_expr ?(prefix = "") target result =
        match target, result with
        | VarTarget ({ declared; name; tau } as ti), (PureExpr e | ImpureExpr e) ->
           if declared && name <> e then
             p "%s = %s;" name e
           else if not declared then
             (p_decl ~prefix ~init:e tau name;
              ti.declared <- true);
           Assigned name
        | NoTarget, ImpureExpr e ->
           p "%s;" e; (* Keep impure exprs like extfuns *)
           NotAssigned
        | (NoTarget, _) -> NotAssigned
        | (VarTarget _, Assigned _) -> result
        | (VarTarget _, NotAssigned) -> assert false
      in

      let p_assign_impure ?prefix target result =
        (* It wouldn't be safe to return the result directly (as a plain
           ImpureExpr) without writing it out, because of sequencing issues
           in expressions like “a := read0(x) + (write0(x); 0)” (we'd end up
           compiling to “WRITE0(x); a = read0(x) + 0;”, which is wrong) *)
        match result with
        | ImpureExpr _ -> p_assign_expr ?prefix target result
        | _ -> result in

      let must_expr = function
        | (PureExpr _ | ImpureExpr _) as expr -> expr
        | Assigned v -> PureExpr v
        | NotAssigned -> assert false in

      let must_value = function
        | Assigned e | PureExpr e | ImpureExpr e -> e
        | NotAssigned -> assert false (* NotAssigned is only return when NoTarget is passed in *) in

      let is_impure_expr = function
        | ImpureExpr _ -> true
        | _ -> false in

      let taint (dependencies: assignment_result list) = function
        | PureExpr s when List.exists is_impure_expr dependencies -> ImpureExpr s
        | other -> other in

      let sp_display_style (dp: Extr.bits_display_style) =
        match dp with
        | DBin -> "prims::bin"
        | DDec -> "prims::dec"
        | DHex -> "prims::hex"
        | DFull -> "prims::full" in

      let p_unop (fn: Extr.PrimTyped.fn1) a1 =
        let open Extr.PrimTyped in
        match fn with
        | Display fn ->
           ImpureExpr
             (match fn with
              | DisplayUtf8 _ -> sprintf "prims::putstring(%s)" a1
              | DisplayValue (_, { display_strings; display_newline; display_style }) ->
                 sprintf "prims::display(%s, { %b, %b, %s })" a1
                   display_strings display_newline (sp_display_style display_style))
        | Conv (tau, fn) ->
           let tau = Cuttlebone.Util.typ_of_extr_type tau in
           PureExpr (match fn with
                     | Pack -> sp_packer ~arg:a1 tau
                     | Unpack -> sp_unpacker ~arg:a1 tau
                     | Ignore -> sprintf "prims::ignore(%s)" a1)
        | Bits1 fn ->
           PureExpr (sprintf "%s(%s)" (cpp_bits1_fn_name fn) a1)
        | Struct1 (sg, idx) ->
           (* Extraction eliminated the single-constructor struct1 inductive (GetField) *)
           let fname, _tau = Cuttlebone.Util.list_nth sg.struct_fields idx in
           let fname = cpp_field_name (Cuttlebone.Util.string_of_coq_string fname) in
           PureExpr (sprintf "%s.%s" a1 fname)
        | Array1 (sg, idx) ->
           PureExpr (sprintf "%s[%d]" a1 (Extr.index_to_nat sg.array_len idx))
      in

      let p_binop target (fn: Extr.PrimTyped.fn2) a1 a2 =
        let open Extr.PrimTyped in
        match fn with
        | Eq (_, negated) ->
           PureExpr (sp_equality ~negated a1 a2)
        | Bits2 fn ->
           PureExpr (sp_binop (cpp_bits2_fn_name fn) a1 a2)
        | Struct2 (sg, idx) ->
           (* Extraction eliminated the single-constructor struct2 inductive (SusbtField) *)
           let sg = Cuttlebone.Util.struct_sig_of_extr_struct_sig sg in
           let fname, _tau = Cuttlebone.Util.list_nth sg.struct_fields idx in
           let tinfo = ensure_target (Struct_t sg) target in
           let res = p_assign_expr (VarTarget tinfo) (PureExpr a1) in
           p "%s.%s = %s;" tinfo.name (cpp_field_name fname) a2;
           res
        | Array2 (_, idx) ->
           PureExpr (sprintf "prims::replace<%d>(%s, %s)" idx a1 a2) in

      let assert_no_shadowing sg (v: var_t) (tau: Extr.type0) v_to_string m =
        if Extr.member_mentions_shadowed_binding Cuttlebone.Util.any_eq_dec sg v tau m then
          let vars = String.concat ", " @@ List.map (v_to_string << fst) sg in
          failwith (sprintf "Variable %s is shadowed by a later binding, but the program references the original binding (full signature: %s)." (v_to_string v) vars) in

      let assert_no_duplicates ~(descr: string) (elements: string list) =
        List.fold_left (fun elems e ->
            if StringSet.mem e elems then
              failwith (sprintf "Duplicate element in %s: %s" descr e)
            else StringSet.add e elems)
          StringSet.empty elements
        |> ignore in

      let rule_name_unprefixed =
        hpp.cpp_rule_names ~prefix:"" rule.rl_name in

      let collect_bindings pos action =
        let rec loop pos bindings = function
          | Extr.Bind (_, tau, _, var, expr, body) when not (List.mem_assoc var bindings) ->
             loop pos ((var, (pos, tau, expr)) :: bindings) body
          | Extr.APos (_, _, Extr.PosAnnot pos, a) ->
             loop (hpp.cpp_pos_of_pos pos) bindings a
          | body -> bindings, (pos, body) in
        let bindings, body = loop pos [] action in
        List.rev bindings, body in

      let package_intfun fn argspec tau =
        { Extr.uint_name = hpp.cpp_fn_names fn.Extr.int_name;
          Extr.uint_argspec = argspec;
          Extr.uint_retType = tau;
          Extr.uint_body = fn.Extr.int_body } in

      (* Table mapping function objects to unique names.  This is reset for each
         rules, because each implementation of a function is specific to one
         rule (this is true at least for rules that may fail, because these need
         to invoke a rule-specific reset function *)
      let internal_functions = Hashtbl.create 20 in

      let lookup_intfun fn argspec tau =
        let intf = package_intfun fn argspec tau in
        intf, Hashtbl.find_opt internal_functions intf in

      let rec p_action
                (at_top: bool)
                (pos: Pos.t) (target: assignment_target)
                (rl: ((pos_t, reg_t) Extr.register_annotation,
                      var_t, fn_name_t, reg_t, _) Extr.action) =
        p_pos pos;
        match rl with
        | Extr.APos (_, _, Extr.HistoryAnnot reg_histories,
                     Extr.Fail (_, _)) ->
           let safe = may_fail_fast reg_histories in
           p "%s();" (fail safe);
           (match target with
            | NoTarget -> NotAssigned
            | VarTarget { declared = true; name; _ } -> Assigned name
            | VarTarget { tau; _ } ->
               PureExpr (sprintf "prims::unreachable<%s>()" (cpp_type_of_type tau)))
        | Extr.Var (sg, v, tau, m) ->
           assert_no_shadowing sg v tau hpp.cpp_var_names m;
           PureExpr (hpp.cpp_var_names v)
        | Extr.Const (_, tau, cst) ->
           let res = PureExpr (sp_value (Cuttlebone.Util.value_of_extr_value tau cst)) in
           if cpp_type_needs_allocation tau then
             let ctarget = gensym_target (Cuttlebone.Util.typ_of_extr_type tau) "cst" in
             must_expr (p_assign_expr ~prefix:"static const" ctarget res)
           else res
        | Extr.Assign (sg, v, tau, m, ex) ->
           assert_no_shadowing sg v tau hpp.cpp_var_names m;
           let vtarget = VarTarget { tau = Cuttlebone.Util.typ_of_extr_type tau;
                                     declared = true; name = hpp.cpp_var_names v } in
           p_assign_and_ignore vtarget (p_action at_top pos vtarget ex);
           PureExpr "prims::tt"
        | Extr.Seq (_, _, a1, a2) ->
           p_assign_and_ignore NoTarget (p_action false pos NoTarget a1);
           p_action at_top pos target a2
        | Extr.Bind _ ->
           let bindings, (pos, body) = collect_bindings pos rl in
           p_declare_target target;
           let p () =
             List.iter (fun (var, (pos, tau, expr)) ->
                 p_bound_var_assign pos tau var expr) bindings;
             (* Force assignment to prevent variable from escaping scope *)
             p_assign_expr target (p_action false pos target body) in
           if at_top then p () else p_scoped "/* bind */" p
        | Extr.If (_, _, cond, tbr, fbr) ->
           p_declare_target target;
           (match reconstruct_switch rl with
            | Some (var, tau, default, branches) ->
               let tau = Cuttlebone.Util.typ_of_extr_type tau in
               p_switch pos target tau var default branches
            | None ->
               let ctarget = gensym_target (Bits_t 1) "test" in
               let cexpr = p_action false pos ctarget cond in
               let tres =
                 p_scoped (sprintf "if (%s)" (must_value cexpr))
                   (fun () -> p_assign_expr target (p_action true pos target tbr)) in
               let fres =
                 if Extr.is_tt fbr then tres
                 else p_scoped "else"
                        (fun () -> p_assign_expr target (p_action true pos target fbr)) in
               assert (tres = fres); tres)
        | Extr.APos (_, _, Extr.HistoryAnnot _,
                     Extr.Read (_, port, reg)) ->
           let r = hpp.cpp_register_sigs reg in
           let pt = match port with P0 -> 0 | P1 -> 1 in
           let expr = sprintf "%s(%s)" (read reg pt) r.reg_name in
           p_assign_impure target (ImpureExpr expr)
        | Extr.APos (_, _, Extr.HistoryAnnot _,
                     Extr.Write (_, port, reg, expr)) ->
           let r = hpp.cpp_register_sigs reg in
           let vt = gensym_target (reg_type r) "v" in
           let v = must_value (p_action false pos vt expr) in
           let pt = match port with P0 -> 0 | P1 -> 1 in
           p "%s(%s, %s);" (write reg pt) r.reg_name v;
           PureExpr "prims::tt"
        | Extr.Unop (_, Extr.PrimTyped.Conv (tau, Extr.PrimTyped.Unpack), a)
             when Extr.(returns_zero a && is_pure a) ->
           p_assign_and_ignore NoTarget (p_action at_top pos NoTarget a);
           PureExpr (sp_initializer (Cuttlebone.Util.typ_of_extr_type tau))
        | Extr.Unop (_, Conv (_, Ignore), a) ->
           p_assign_and_ignore NoTarget (p_action false pos NoTarget a);
           (PureExpr "prims::tt")
        | Extr.Unop (_, fn, a) ->
           let fsig = Extr.PrimSignatures.coq_Sigma1 fn in
           let a = p_action false pos (gensym_target (Cuttlebone.Util.argType 1 fsig 0) "x") a in
           register_subtypes program_info (Cuttlebone.Util.retSig fsig);
           p_assign_impure target (taint [a] (p_unop fn (must_value a)))
        | Extr.Binop (_, fn, a1, a2) ->
           let fsig = Extr.PrimSignatures.coq_Sigma2 fn in
           let a1 = p_action false pos (maybe_gensym_target target (Cuttlebone.Util.argType 2 fsig 0) "x") a1 in
           let a2 = p_action false pos (gensym_target (Cuttlebone.Util.argType 2 fsig 1) "y") a2 in
           register_subtypes program_info (Cuttlebone.Util.retSig fsig);
           p_assign_impure target (taint [a1; a2] (p_binop target fn (must_value a1) (must_value a2)))
        | Extr.ExternalCall (_, fn, a) ->
           let (ffi, kind) = hpp.cpp_ext_sigs fn in
           let a = p_action false pos (gensym_target ffi.ffi_argtype "x") a in
           Hashtbl.replace program_info.pi_ext_funcalls ffi ();
           (* See ‘Read’ case for why returning just ImpureExpr isn't safe *)
           let expr = cpp_ext_funcall ffi.ffi_name kind (must_value a) in
           p_assign_impure target (ImpureExpr expr)
        | Extr.InternalCall (_, tau, argspec, fn, rev_args) ->
           let fn_name = match snd (lookup_intfun fn argspec tau) with
             | Some fn -> fn
             | None -> assert false in
           let args = Extr.cfoldl (fun (argname, tau) arg argstrs ->
                          let tau = Cuttlebone.Util.typ_of_extr_type tau in
                          let argname = hpp.cpp_var_names argname in
                          let target = gensym_target tau argname in
                          must_value (p_action false pos target arg) :: argstrs)
                        argspec rev_args [] in
           (* FIXME need the type of the return value in the macro to know what kind of parameter to declare *)
           (* See ‘Read’ case for why returning just ImpureExpr isn't safe *)
           let args = String.concat ", " (fn_name :: args) in
           let invocation = sprintf "%s(%s)" call args in
           p_assign_impure target (ImpureExpr invocation)
        | Extr.APos (_, _, Extr.PosAnnot pos, a) ->
           p_action at_top (hpp.cpp_pos_of_pos pos) target a
        | Extr.Fail (_, _) -> while true do () done; failwith "Missing annotation on fail"
        | Extr.Read (_, _, _) -> failwith "Missing annotation on read"
        | Extr.Write (_, _, _, _) -> failwith "Missing annotation on write"
        | Extr.APos (_, _, Extr.HistoryAnnot _, _) -> failwith "Unexpected annotation"
      and p_switch pos target tau var default branches =
        let rec loop = function
          | [] ->
             let res = p_scoped "default:" (fun () -> p_assign_expr target (p_action true pos target default)) in
             p "break;"; (* Ensure that we don't print an empty ‘default:’ case *)
             res
          | (const, action) :: branches ->
             p_scoped (sprintf "case %s:" (sp_value ~immediate:true const))
               (fun () -> p_assign_and_ignore target (p_action true pos target action));
             p "break;";
             loop branches in
        let varname = hpp.cpp_var_names var in
        let discriminand = match tau with
          | Bits_t _ -> sprintf "%s.v" varname
          | _ -> varname in
        p_scoped (sprintf "switch (%s)" discriminand) (fun () ->
            loop branches)
      and p_bound_var_assign pos tau v expr =
        let needs_tmp = Extr.action_mentions_var Cuttlebone.Util.any_eq_dec v expr in
        let tau = Cuttlebone.Util.typ_of_extr_type tau in
        let vtarget = VarTarget { tau; declared = false; name = hpp.cpp_var_names v } in
        let expr =
          if needs_tmp then
            (* ‘int x = x + 1;’ doesn't work in C++ (basic.scope.pdecl), so if
               the rhs uses a variable with name ‘v’ we need a temp variable. *)
            let vtmp = gensym_target tau "tmp" in
            must_expr (p_assign_expr vtmp (p_action false pos vtmp expr))
          else p_action false pos vtarget expr in
        p_assign_and_ignore vtarget expr
      and p_assign_and_ignore target expr =
        ignore (p_assign_expr target expr) in

      let p_special_fn kind ?(args=rule_name_unprefixed) p_body =
        let virtual_flag = if rule.rl_external then "virtual " else "" in
        p_scoped (sprintf "%sDEF_%s(%s)" virtual_flag kind args) p_body in

      let p_reset_commit () =
        if not use_dynamic_log then
          (p_special_fn "RESET" p_reset;
           nl ();
           p_special_fn "COMMIT" p_commit;
           nl ()) in

      let p_rule_body () =
        p_special_fn "RULE" (fun () ->
            if use_dynamic_log then (p "dynamic_log_t<%d> dlog{};" rule_max_log_size; nl ());
            (try
               p_assign_and_ignore NoTarget (p_action true Pos.Unknown NoTarget rule.rl_body);
             with Failure msg ->
               let msg = sprintf "In %s: %s" rule_name_unprefixed msg in
               Printexc.raise_with_backtrace (Failure msg) (Printexc.get_raw_backtrace ()));
            nl ();
            p "%s();" commit) in

      let collect_intfuns pos (action: (_, var_t, fn_name_t, reg_t, _) Extr.action) =
        let fns = ref [] in
        let ensure_fresh fn =
          let rec loop counter =
            let nm = sprintf "%s_%d" fn counter in
            if not (Hashtbl.mem internal_fnames nm) then
              let () = Hashtbl.add internal_fnames nm () in nm
            else
              loop (counter + 1) in
          loop 0 in
        let register_intfun pos fn argspec tau =
          assert_no_duplicates ~descr:"argument list"
            (List.map (fun (v, _) -> hpp.cpp_var_names v) argspec);
          match lookup_intfun fn argspec tau with
          | _, Some _ -> ()
          | intf, None ->
             let nm = ensure_fresh (hpp.cpp_fn_names fn.Extr.int_name) in
             fns := (pos, nm, intf) :: !fns;
             Hashtbl.add internal_functions intf nm; in
        let rec loop pos = function
          | Extr.Fail _
            | Extr.Var _
            | Extr.Const _
            | Extr.Read (_, _, _) -> ()
          | Extr.Assign (_, _, _, _, a)
            | Extr.Write (_, _, _, a)
            | Extr.Unop (_, _, a)
            | Extr.ExternalCall (_, _, a)
            | Extr.APos (_, _, _, a) ->
             loop pos a
          | Extr.Seq (_, _, a1, a2)
            | Extr.Bind (_, _, _, _, a1, a2)
            | Extr.Binop (_, _, a1, a2) ->
             loop pos a1;
             loop pos a2
          | Extr.If (_, _, c, tbr, fbr) ->
             loop pos c;
             loop pos tbr;
             loop pos fbr
          | Extr.InternalCall (_, tau, argspec, fn, rev_args) ->
             register_intfun pos fn argspec tau;
             Extr.cfoldr (fun _ _ arg () -> loop pos arg) argspec rev_args ();
             loop pos fn.Extr.int_body in
        loop pos action;
        List.rev !fns in

      let p_intfun (pos, name, intf) =
        let sp_arg (nm, tau) =
          let tau = Cuttlebone.Util.typ_of_extr_type tau in
          sprintf "%s %s" (cpp_type_of_type tau) (hpp.cpp_var_names nm) in
        let ret_tau = Cuttlebone.Util.typ_of_extr_type intf.Extr.uint_retType in
        let ret_type = cpp_type_of_type ret_tau in
        let ret_arg = sprintf "%s %s" ret_type "&_ret" in
        let args = String.concat ", " @@ name :: ret_arg :: List.map sp_arg intf.Extr.uint_argspec in
        p "DECL_FN(%s, %s)" name ret_type;
        p_special_fn "FN" ~args (fun () ->
            let target = VarTarget { tau = ret_tau; declared = true; name = "_ret" } in
            p_assign_and_ignore target (p_action true pos target intf.uint_body);
            p "return true;") in

      p "#define RULE_NAME %s" rule_name_unprefixed;
      p_reset_commit ();
      iter_sep nl p_intfun (collect_intfuns Pos.Unknown rule.rl_body);
      p_rule_body ();
      p "#undef RULE_NAME" in

    let p_initial_state () =
      (* This is a function instead of a variable to avoid polluting GDB's output *)
      p_fn ~typ:"static constexpr state_t" ~name:"initial_state" ~args:"" (fun () ->
          p_scoped "state_t init" ~terminator:";" (fun () ->
              iter_all_registers (fun rn ->
                  p ".%s = %s," rn.reg_name (sp_value rn.reg_init)));
          p "return init;") in

    let p_finish () =
      p_fn ~typ:"void" ~name:"finish"
        ~args:"cuttlesim::exit_info exit_config, int exit_code" (fun () ->
          p "meta.finished = true;";
          p "meta.exit_config = exit_config;";
          p "meta.exit_code = exit_code;");
      nl();
      p_fn ~typ:"bool" ~name:"finished" (fun () ->
          p "return meta.finished;") in

    let p_snapshot () =
      p_fn ~typ:"snapshot_t" ~name:"snapshot" ~annot:" const" (fun () ->
          (* Return by value to allow snapshots to outlive their simulation. *)
          p "return snapshot_t(Log.snapshot(), meta);") in

    let p_constructor () =
      p_fn ~typ:"explicit" ~name:hpp.cpp_classname
        ~args:"const state_t init = initial_state()"
        ~annot:" : log(init), Log(init), extfuns{}, meta{}"
        (fun () -> p_ifnminimal (fun () ->
                       p "rng.seed(cuttlesim::random_seed);")) in

    let rec p_scheduler pos s =
      p_pos pos;
      match s with
      | Extr.Done -> ()
      | Extr.Cons (rl_name, s) ->
         p "%s();" (hpp.cpp_rule_names rl_name);
         p_scheduler pos s
      | Extr.Try (rl_name, s1, s2) ->
         p_scoped (sprintf "if (%s())" (hpp.cpp_rule_names rl_name)) (fun () ->
             p_scheduler pos s1);
         p_scoped "else" (fun () -> p_scheduler pos s2)
      | Extr.SPos (pos, s) ->
         p_scheduler (hpp.cpp_pos_of_pos pos) s in

    let p_strobe () =
      p "_virtual void strobe() const {}" in

    let p_cycle_function pscheduler =
      p "meta.cycle_id++;";
      p "log.rwset = Log.rwset = rwset_t{};";
      pscheduler ();
      p "strobe();" in

    let p_cycle () =
      p_fn ~typ:"void" ~name:"cycle" (fun () ->
          p_cycle_function (fun () ->
              p_scheduler Pos.Unknown hpp.cpp_scheduler)) in

    let p_cycle_randomized () =
      let nrules = List.length hpp.cpp_rules in
      let prefix = sprintf "%s::" hpp.cpp_classname in
      p "typedef bool (%s*rule_ptr)();" prefix;
      p_fn ~typ:"void" ~name:"cycle_randomized" (fun () ->
          p_cycle_function (fun () ->
              if nrules > 0 then
                let decl = sprintf "static constexpr rule_ptr rules[%d]" nrules in
                p_scoped decl ~terminator:";" (fun () ->
                    iter_sep (fun () -> p ",") (fun { rl_name; _ } ->
                        pr "&%s%s" prefix (hpp.cpp_rule_names rl_name))
                      hpp.cpp_rules);
                p "(this->*rules[uniform(rng)])();")) in

    let run_typ =
      sprintf "_flatten %s&" hpp.cpp_classname in

    let p_cycle_loop pbody =
      p_scoped "for (std::uint_fast64_t cycle_id = 0;
                cycle_id < ncycles && !meta.finished;
                cycle_id++)"
        pbody in

    let p_run name cycle =
      p_fn ~typ:run_typ ~name ~args:"std::uint_fast64_t ncycles" (fun () ->
          p_cycle_loop (fun () -> p "%s();" cycle);
          p "return *this;") in

    let p_trace name cycle =
      p_fn ~typ:run_typ ~name
        ~args:"std::string fname, std::uint_fast64_t ncycles" (fun () ->
          p "std::ofstream vcd(fname);";
          p "state_t::vcd_header(vcd);";
          p "state_t latest = Log.snapshot();";
          p "latest.vcd_dumpvars(meta.cycle_id, vcd, latest, true);";
          p_cycle_loop (fun () ->
              p "%s();" cycle;
              p "state_t current = Log.snapshot();";
              p "current.vcd_dumpvars(meta.cycle_id, vcd, latest, false);";
              p "latest = current;");
          p "return *this;") in

    p_sim_class (fun () ->
        p "public:";
        p_state_t ();
        nl ();
        p_snapshot_t ();
        nl ();

        p "protected:";
        p_rwset_t ();
        nl ();
        p_log_t ();
        nl ();
        if use_dynamic_logs then
          (p_dynamic_log_t ();
           nl ());
        p "log_t log;";
        p "log_t Log;";
        p "extfuns_t extfuns;";
        p "cuttlesim::sim_metadata meta;";
        nl ();
        p_ifnminimal (fun () ->
            p "std::default_random_engine rng{};";
            p "std::uniform_int_distribution<int> uniform{0, %d};"
              (max 0 (List.length hpp.cpp_rules - 1)));
        nl ();
        iter_sep nl p_rule hpp.cpp_rules;
        nl ();

        p "public:";
        p_finish ();
        nl ();
        p_snapshot ();
        nl ();
        p_initial_state ();
        nl ();
        p_constructor ();
        nl ();
        p_strobe ();
        nl ();
        p_cycle ();
        nl ();
        p_run "run" "cycle";
        nl ();
        p_ifnminimal (fun () ->
            p_cycle_randomized ();
            nl ();
            p_run "run_randomized" "cycle_randomized";
            nl ();
            p_trace "trace" "cycle";
            nl ();
            p_trace "trace_randomized" "cycle_randomized")) in

  let with_output_to_buffer (pbody: unit -> unit) =
    let buf = set_buffer (Buffer.create 4096) in
    pbody ();
    set_buffer buf in

  let p_hpp () =
    let impl = with_output_to_buffer p_impl in
    let typedefs = with_output_to_buffer p_type_declarations in
    p_includeguard (fun () ->
        p_preamble ();
        nl ();
        p_buffer typedefs;
        nl ();
        p_buffer impl;
        nl ()) in

  let p_extfun_decl { ffi_name; ffi_argtype; ffi_rettype } =
    let sp_arg typ = sprintf "const %s arg" (cpp_type_of_type typ) in
    let typ = cpp_type_of_type ffi_rettype in
    p_comment "%s %s(%s);" typ ffi_name (sp_arg ffi_argtype) in

  let sp_prelude_stub () =
    with_output_to_buffer (fun () ->
        p_scoped "class extfuns" ~terminator:";" (fun () ->
            p "public:";
            p_comment "External methods (if any) should be implemented here.";
            p_comment "Approximate signatures are provided below for convenience.";
            let fns = List.of_seq (Hashtbl.to_seq_keys program_info.pi_ext_funcalls) in
            List.iter p_extfun_decl (List.sort compare fns))) in

  let p_cpp () =
    let extfuns =
      match hpp.cpp_extfuns with
      | Some cpp -> cpp
      | None -> if Hashtbl.length program_info.pi_ext_funcalls = 0
                then "struct extfuns {};"
                else Buffer.contents (sp_prelude_stub ()) in

    let markers =
      [("__CUTTLEC_MODULE_NAME__", hpp.cpp_module_name);
       ("__CUTTLEC_EXTFUNS__", extfuns)] in
    let contents =
      Common.replace_strings Resources.cuttlesim_cpp markers in
    Buffer.add_string !buffer contents in

  let buf_cpp = with_output_to_buffer p_cpp in
  let buf_hpp = with_output_to_buffer p_hpp in
  { co_modname = hpp.cpp_module_name;
    co_hpp = buf_hpp;
    co_cpp = buf_cpp }

let cpp_rule_of_action reg_histories (rl_name, (kind, rl_body)) =
  { rl_external = kind = `ExternalRule; rl_name; rl_body;
    rl_reg_histories = reg_histories rl_name }

let input_of_compile_unit (cu: 'f Cuttlebone.Compilation.compile_unit) =
  let rulemap r =
    snd (List.assoc r cu.c_rules) in
  let reg_histories, annotated_rules, register_kinds =
    Cuttlebone.Util.compute_register_histories
      Cuttlebone.Compilation._R cu.c_registers
      (List.map fst cu.c_rules) rulemap cu.c_scheduler in
  let swap_body (name, (kind, _))
      : (_ * (_ * (_, Common.var_t, Common.fn_name_t, Common.reg_signature, 'c)
                    Cuttlebone.Extr.annotated_rule)) =
    (name, (kind, annotated_rules name)) in
  { cpp_classname = cu.c_modname;
    cpp_module_name = cu.c_modname;
    cpp_pos_of_pos = cu.c_pos_of_pos;
    cpp_var_names = (fun x -> x);
    cpp_fn_names = (fun x -> x);
    cpp_rule_names = (fun ?prefix:_ rl -> rl);
    cpp_scheduler = cu.c_scheduler;
    cpp_rules = List.map (cpp_rule_of_action reg_histories << swap_body) cu.c_rules;
    cpp_registers = Array.of_list cu.c_registers;
    cpp_register_sigs = (fun r -> r);
    cpp_register_kinds = register_kinds;
    cpp_ext_sigs = (fun f -> f, `Function); (* FIXME add syntax for methods *)
    cpp_extfuns = cu.c_cpp_preamble; }

let cpp_rule_of_koika_package_rule (kp: _ Extr.koika_package_t)
      (reg_histories: 'rn -> 'rg -> _) (annotated_rules: 'rn -> _) (rn: 'rn) =
  let kind rn = if kp.koika_rule_external rn then `ExternalRule else `InternalRule in
  cpp_rule_of_action reg_histories (rn, (kind rn, annotated_rules rn))

let input_of_sim_package
      (kp: ('pos_t, 'var_t, 'fn_name_t, 'rule_name_t, 'reg_t, 'ext_fn_t) Extr.koika_package_t)
      (sp: ('ext_fn_t) Extr.sim_package_t)
    : ('pos_t, 'var_t, 'fn_name_t, 'rule_name_t, 'reg_t, 'ext_fn_t) cpp_input_t =
  let open Cuttlebone in
  let rule_names =
    Extr.scheduler_rules kp.koika_scheduler |> Util.dedup in
  let reg_histories, annotated_rules, register_kinds =
    Util.compute_register_histories
      kp.koika_reg_types kp.koika_reg_finite.finite_elements
      rule_names kp.koika_rules kp.koika_scheduler in
  let classname = Util.string_of_coq_string kp.koika_module_name in
  let ext_fn_sigs f =
    let spec = sp.sp_ext_fn_specs f in
    let name = Util.string_of_coq_string spec.efs_name in
    let fsig = Util.ffi_sig_of_extr_external_sig name (kp.koika_ext_fn_types f) in
    let kind = if spec.efs_method then `Method else `Function in
    (fsig, kind) in
  let registers = kp.koika_reg_finite.finite_elements in
  { cpp_classname = classname;
    cpp_module_name = classname;
    cpp_pos_of_pos = (fun _ -> Pos.Unknown);
    cpp_var_names = (fun x -> Util.string_of_coq_string (kp.koika_var_names.show0 x));
    cpp_fn_names = (fun x -> Util.string_of_coq_string (kp.koika_fn_names.show0 x));
    cpp_rule_names = (fun ?prefix:_ rn ->
      Util.string_of_coq_string (kp.koika_rule_names.show0 rn));
    cpp_scheduler = kp.koika_scheduler;
    cpp_rules = List.map (cpp_rule_of_koika_package_rule kp reg_histories annotated_rules) rule_names;
    cpp_registers = Array.of_list registers;
    cpp_register_sigs = Util.reg_sigs_of_koika_package kp;
    cpp_register_kinds = register_kinds;
    cpp_ext_sigs = ext_fn_sigs;
    cpp_extfuns = (match sp.sp_prelude with
                   | None -> None
                   | Some s -> Some (Util.string_of_coq_string s)); }

let flags_standard =
  ["--std=c++14"]
let flags_opt =
  ["-O3"; "-march=native"; "-U_FORTIFY_SOURCE"; "-D_FORTIFY_SOURCE=0"; "-fno-stack-protector"]
let flags_warnings =
  ["-Wall"; "-Wextra"]

let compile_cpp fname =
  let srcname = fname ^ ".cpp" in
  let exename = fname ^ ".exe" in
  let flags = flags_standard @ flags_warnings @ flags_opt in
  Common.command ~verbose:true ~elapsed:true "g++" (flags @ [srcname; "-o"; exename])

let write_formatted fpath_noext ext buf =
  let fname = fpath_noext ^ ext in
  Common.with_output_to_file fname Buffer.output_buffer buf

let write_preamble dpath =
  let fpath = Filename.concat dpath cuttlesim_hpp_fname in
  Common.with_output_to_file fpath output_string cuttlesim_hpp

let write_output target_dpath (kind: [< `Cpp | `Hpp | `Opt]) ({ co_modname; co_hpp; co_cpp }: cpp_output_t) =
  let fpath_noext = Filename.concat target_dpath co_modname in
  if kind = `Hpp || kind = `Opt then begin
      write_preamble target_dpath;
      write_formatted fpath_noext ".hpp" co_hpp end;
  if kind = `Cpp || kind = `Opt then
    write_formatted fpath_noext ".cpp" co_cpp;
  if kind = `Opt then
    compile_cpp fpath_noext

let main target_dpath (kind: [< `Cpp | `Hpp | `Opt]) (cu: _ cpp_input_t) =
  write_output target_dpath kind (compile cu)
