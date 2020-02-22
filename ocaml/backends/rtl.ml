(*! Generic RTL backend !*)
open Common
open Cuttlebone
open Cuttlebone.Util
open Cuttlebone.Graphs

open Printf

let debug = false
let add_debug_annotations = false
let omit_reset_line = false
let compile_bundles_internally = false

type node_metadata =
  { shared: bool; circuit: circuit' }

type metadata_map = (int, node_metadata) Hashtbl.t

type expr =
  | EPtr of node * string option
  | EName of string
  | EConst of Common.bits_value
  | EUnop of Extr.PrimTyped.fbits1 * node
  | EBinop of Extr.PrimTyped.fbits2 * node * node
  | EMux of node * node * node
and entity =
  | Expr of expr
  | Module of { name: string;
                internal: bool;
                inputs: input_pin list;
                outputs: output_pin list }
and node =
  { tag: int;
    size: int;
    entity: entity;
    annots: string list;
    mutable kind: node_kind }
and node_kind =
  | Unique
  | Shared
  | Printed of { name: string }
and input_pin =
  { ip_name: string; ip_node: node }
and output_pin =
  { op_name: string; op_wire: string; op_sz: int }

type node_map = (int, node) Hashtbl.t
type pin_set = (string, [`Input | `Output] * int) Hashtbl.t

let may_share = function
  | Module _ | Expr (EUnop _ | EBinop _ | EMux _) -> true
  | _ -> false

let fn1_sz fn =
  let fsig = Cuttlebone.Extr.PrimSignatures.coq_Sigma1 (Bits1 fn) in
  typ_sz (Cuttlebone.Util.retSig fsig)

let fn2_sz fn =
  let fsig = Cuttlebone.Extr.PrimSignatures.coq_Sigma2 (Bits2 fn) in
  typ_sz (Cuttlebone.Util.retSig fsig)

let rwdata_circuits (rwd: Cuttlebone.Graphs.rwdata) =
  let open Cuttlebone.Extr in
  [(Rwdata_r0, rwd.read0); (Rwdata_r1, rwd.read1);
   (Rwdata_w0, rwd.write0); (Rwdata_w1, rwd.write1);
   (Rwdata_data0, rwd.data0); (Rwdata_data1, rwd.data1)]

let compute_circuit_metadata (metadata: metadata_map) (c: circuit) =
  let rec iter c =
    let open Hashcons in
    match Hashtbl.find_opt metadata c.tag with
    | Some _ ->
       Hashtbl.replace metadata c.tag { shared = true; circuit = c.node }
    | None ->
       iter' c.node;
       assert (not (Hashtbl.mem metadata c.tag)); (* No cycles *)
       Hashtbl.replace metadata c.tag { shared = false; circuit = c.node }
  and iter' (node: circuit') =
    match node with
    | CMux (_, s, c1, c2) -> iter s; iter c1; iter c2
    | CConst _ -> ()
    | CReadRegister _ -> ()
    | CUnop (_, c1) -> iter c1
    | CBinop (_, c1, c2) -> iter c1; iter c2
    | CExternal (_, c) -> iter c
    | CBundle (_, ios) ->
       List.iter (fun (_, rwd) ->
           List.iter (fun (_, c) -> iter c) (rwdata_circuits rwd))
         ios
    | CBundleRef (_, c, _) -> iter c
    | CAnnot (_, _, c) -> iter c in
  ignore (iter c)

let rwdata_field_to_string (field: Extr.rwdata_field) =
  match field with
  | Rwdata_r0 -> "read0"
  | Rwdata_r1 -> "read1"
  | Rwdata_w0 -> "write0"
  | Rwdata_w1 -> "write1"
  | Rwdata_data0 -> "data0"
  | Rwdata_data1 -> "data1"

let rwcircuit_to_string (rwc: rwcircuit) =
  match rwc with
  | Rwcircuit_canfire -> "_canfire"
  | Rwcircuit_rwdata (reg, field) ->
     sprintf "%s_%s" reg.reg_name (rwdata_field_to_string field)

(* Our state *before* calling the external rule is an output of this module, and
   the resulting state produced by the rule is an input of this module. *)
let before_prefix, after_prefix = "output", "input"

let field_name instance field =
  sprintf "%s_%s" instance field

let node_of_circuit (metadata: metadata_map) (cache: node_map) (ios: pin_set) (c: circuit) =
  let fresh_node size entity =
    { tag = -1; size; annots = []; entity; kind = Unique } in
  let rec lift ({ tag; node = c'; _ }: circuit) =
    match Hashtbl.find_opt cache tag with
    | Some node -> node
    | None ->
       let size, annots, entity = lift' c' in
       let n = { tag; size; entity; annots; kind = Unique } in
       let shared = (Hashtbl.find metadata tag).shared in
       if shared && may_share entity then n.kind <- Shared;
       Hashtbl.replace cache n.tag n;
       n
  and lift' (c: circuit') =
    match c with
    | CMux (sz, s, c1, c2) -> sz, [], Expr (EMux (lift s, lift c1, lift c2))
    | CConst c -> Array.length c, [], Expr (EConst c)
    | CReadRegister r -> typ_sz (reg_type r), [], Expr (EName (r.reg_name))
    | CUnop (f, c1) -> fn1_sz f, [], Expr (EUnop (f, lift c1))
    | CBinop (f, c1, c2) -> fn2_sz f, [], Expr (EBinop (f, lift c1, lift c2))
    | CExternal (f, c) ->
       let size = typ_sz f.ffi_rettype in
       let inputs = [{ ip_name = "arg"; ip_node = lift c }] in
       let outputs = [{ op_name = "out"; op_wire = "out"; op_sz = typ_sz f.ffi_rettype }] in
       let mod_ent = Module { name = f.ffi_name; internal = true; inputs; outputs } in
       size, [], Expr (EPtr (fresh_node size mod_ent, Some "out"))
    | CBundle (name, bundle_ios) ->
       let name = "rule_" ^ name in
       let reg_ios = List.map inputs_outputs_of_module_io bundle_ios in
       let inputs, outputs = reg_ios |> List.concat |> List.split in
       let cf_name = rwcircuit_to_string Rwcircuit_canfire in
       let outputs = { op_name = field_name after_prefix cf_name; op_wire = cf_name; op_sz = 1 } :: outputs in
       (* The module's outputs are our inputs, and vice-versa *)
       List.iter (fun op -> Hashtbl.replace ios (field_name name op.op_name) (`Input, op.op_sz)) outputs;
       List.iter (fun ip -> Hashtbl.replace ios (field_name name ip.ip_name) (`Output, ip.ip_node.size)) inputs;
       0, [], Module { name; internal = compile_bundles_internally; inputs; outputs }
    | CBundleRef (sz, c, field) ->
       sz, [], Expr (EPtr (lift c, Some (field_name after_prefix (rwcircuit_to_string field))))
    | CAnnot (sz, annot, c) ->
       let ann = if annot = "" then [] else [annot] in
       match lift c with
       | { kind = Unique; annots; entity; _ } -> sz, ann @ annots, entity
       | n -> sz, ann, Expr (EPtr (n, None))
  and inputs_outputs_of_module_io (reg, rwd) =
    List.map (fun (field, c) ->
        let ip_node = lift c in
        let nm = rwcircuit_to_string (Rwcircuit_rwdata (reg, field)) in
        ({ ip_name = field_name before_prefix nm; ip_node },
         { op_name = field_name after_prefix nm; op_wire = nm; op_sz = ip_node.size }))
      (rwdata_circuits rwd) in
  lift c

module Debug = struct
  let unop_to_str =
    let open Cuttlebone.Extr.PrimTyped in
    function
    | Not _ -> "not"
    | SExt (_, _) -> "sext"
    | ZExtL (_, _) -> "zextl"
    | ZExtR (_, _) -> "zextr"
    | Repeat (_, _) -> "repeat"
    | Slice (_, _, _) -> "slice"
    | Lowered _ -> "lowered"

  let binop_to_str =
    let open Cuttlebone.Extr.PrimTyped in
    function
    | And _ -> "and"
    | Or _ -> "or"
    | Xor _ -> "xor"
    | Lsl (_, _) -> "lsl"
    | Lsr (_, _) -> "lsr"
    | Asr (_, _) -> "asr"
    | Concat (_, _) -> "concat"
    | Sel _ -> "sel"
    | SliceSubst (_, _, _) -> "slicesubst"
    | IndexedSlice (_, _) -> "indexedslice"
    | Plus _ -> "plus"
    | Minus _ -> "minus"
    | EqBits (_, _) -> "eqbits"
    | Compare (_, _, _) -> "compare"

  let expr_to_str = function
    | EPtr (n, Some field) -> sprintf "EPtr (%d, %s)" n.tag field
    | EPtr (n, None) -> sprintf "EPtr (%d, None)" n.tag
    | EName n -> sprintf "EName \"%s\"" n
    | EConst cst -> sprintf "EConst %s" (string_of_bits cst)
    | EMux (s, c1, c2) -> sprintf "EMux (%d, %d, %d)" s.tag c1.tag c2.tag
    | EUnop (f, c) -> sprintf "EUnop (%s, %d)" (unop_to_str f) c.tag
    | EBinop (f, c1, c2) -> sprintf "EBinop (%s, %d, %d)" (binop_to_str f) c1.tag c2.tag

  let entity_to_str = function
    | Expr e -> expr_to_str e
    | Module { name; internal; inputs; outputs } ->
       sprintf "Module (%s, internal=%b, [%s], [%s])" name internal
         (String.concat "; "
            (List.map (fun { ip_name; ip_node } ->
                 sprintf "(%s, %d)" ip_name ip_node.tag) inputs))
         (String.concat "; "
            (List.map (fun { op_name; _ } ->
                 sprintf "%s" op_name) outputs))

  let node_kind_to_str = function
    | Unique -> "Unique"
    | Shared -> "Shared"
    | Printed { name } -> sprintf "Printed { name = \"%s\" }" name

  let node_to_str { tag; entity; annots; kind; _ } =
    sprintf "{ tag=%d; kind=%s; entity=%s; annots=[%s] }"
      tag (node_kind_to_str kind) (entity_to_str entity) (String.concat "; " annots)

  let circuit_to_str =
    let open Cuttlebone.Graphs in
    function
    | CMux (_, s, c1, c2) -> sprintf "CMux (%d, %d, %d)" s.tag c1.tag c2.tag
    | CConst cst -> sprintf "CConst %s" (string_of_bits cst)
    | CReadRegister r -> sprintf "CReadRegister %s" r.reg_name
    | CUnop (f, c) -> sprintf "CUnop (%s, %d)" (unop_to_str f) c.tag
    | CBinop (f, c1, c2) -> sprintf "CBinop (%s, %d, %d)" (binop_to_str f) c1.tag c2.tag
    | CExternal (_, c) -> sprintf "CExternal (_, %d)" c.tag
    | CBundle (_, _) -> sprintf "CBundle"
    | CBundleRef (_, _, _) -> sprintf "CBundleRef"
    | CAnnot (_, a, c) -> sprintf "CAnnot \"%s\" %d" a c.tag

  let iter_ordered f tbl =
    List.iter (fun (k, v) -> f k v)
      (List.sort poly_cmp (List.of_seq (Hashtbl.to_seq tbl)))

  let print_node_cache cache =
    if debug then
      iter_ordered (fun tag node ->
          eprintf "%d → %s\n" tag (node_to_str node))
        cache

  let print_metadata metadata =
    if debug then
      iter_ordered (fun tag { shared; circuit } ->
          eprintf "%d → { shared=%b; circuit=%s }\n"
            tag shared (circuit_to_str circuit))
        metadata

  let annotate annots s =
    if add_debug_annotations then
      match annots with
      | [] -> s
      | ans -> sprintf "/*<%s>*/%s" (String.concat "; " ans) s
    else s
end

let compute_roots_metadata graph_roots =
  let metadata = Hashtbl.create 500 in
  List.iter (fun c -> compute_circuit_metadata metadata c.root_circuit) graph_roots;
  Debug.print_metadata metadata;
  metadata

let translate_roots metadata graph_roots =
  let ios = Hashtbl.create 50 in
  let cache = Hashtbl.create 500 in
  let translate_root { root_reg; root_circuit } =
    (root_reg.reg_name,
     Cuttlebone.Util.bits_of_value root_reg.reg_init,
     node_of_circuit metadata cache ios root_circuit) in
  let roots = List.map translate_root graph_roots in
  Debug.print_node_cache cache;
  roots, ios

let gensym_next, gensym_reset =
  make_gensym ""

let name_node (n: node) =
  let rec last = function
    | [] -> ""
    | [lst] -> lst
    | _ :: tl -> last tl in
  gensym_next ("_" ^ last n.annots)

let unlowered () =
  failwith "sext, zextl, zextr, etc. must be elaborated away by the compiler."

module type RTLBackend = sig
  val p_module : modname:string -> out_channel -> circuit_graph -> unit
end

module Verilog : RTLBackend = struct
  let p_stmt out indent fmt =
    fprintf out "%s" (String.make indent '\t');
    kfprintf (fun out -> fprintf out ";\n") out fmt

  let p_assign out name expr =
    p_stmt out 1 "assign %s = %s" name expr

  let sp_type kind sz =
    if sz = 1 then kind else sprintf "%s[%d:0]" kind (pred sz)

  let p_decl out kind sz ?expr name =
    let typ = sp_type kind sz in
    match expr with
    | None -> p_stmt out 1 "%s %s" typ name
    | Some expr -> p_stmt out 1 "%s %s = %s" typ name expr

  let precedence = function
    | EName _ | EConst _ -> -1
    | EPtr _ -> -2
    | EUnop (Slice _, _) | EBinop ((Sel _ | IndexedSlice _), _, _) -> -3
    | EUnop (Not _, _) -> -4
    | EBinop (Concat _, _, _) -> -5
    | EUnop (Repeat _, _) -> -6
    | EBinop ((Plus _ | Minus _), _, _) -> -7
    | EBinop ((Lsl _ | Lsr _ | Asr _), _, _) -> -8
    | EBinop (Compare (_, _, _), _, _) -> -9
    | EBinop (EqBits _, _, _) -> -10
    | EBinop (And _, _, _) -> -11
    | EBinop (Xor _, _, _) -> -12
    | EBinop (Or _, _, _) -> -13
    | EMux (_, _, _) -> -14
    | EUnop ((SExt _ | ZExtL _ | ZExtR _ | Lowered _), _)
      | EBinop (SliceSubst _, _, _) -> unlowered ()

  let complex_expr = function
    | EPtr _ | EName _ -> false
    (* Yosys doesn't support chained selects (x[4 +: 32][3 +: 2]) *)
    | EUnop (Slice _, _) | EBinop ((Sel _ | IndexedSlice _), _, _) -> true
    | EUnop _ | EBinop _ | EMux _ | EConst _ -> true

  let sp_cast signed p () x =
    sprintf (if signed then "$signed(%a)" else "$unsigned(%a)") p x

  let rec p_expr out (e: expr) =
    let lvl = precedence e in
    let sp_str () s = s in
    let p () n = snd (p_node out lvl n) in
    let pr () n = snd (p_node ~restricted_ctx:true out min_int n) in
    let p0 () n = snd (p_node out min_int n) in
    let sp fmt = ksprintf (fun s -> (lvl, s)) fmt in
    match e with
    | EPtr (n, None) -> (lvl, p () n)
    | EPtr (n, Some field) -> let nm = p () n in (lvl, field_name nm field)
    | EName name -> (lvl, name)
    | EConst cst -> (lvl, string_of_bits cst)
    | EUnop (f, e) ->
       (match f with
        | Not _ -> sp "~%a" p e
        | Repeat (_, times) -> sp "{%d{%a}}" times p0 e
        | Slice (_, offset, slice_sz) -> sp "%a[%d +: %d]" pr e offset slice_sz
        | SExt _ | ZExtL _ | ZExtR _ | Lowered _ -> unlowered ())
    | EBinop (f, e1, e2) ->
       (match f with
        | Plus _ -> sp "%a + %a" p e1 p e2
        | Minus _ -> sp "%a - %a" p e1 p e2
        | Compare(s, CLt, _) -> sp "%a < %a" (sp_cast s p) e1 (sp_cast s p) e2
        | Compare(s, CGt, _) -> sp "%a > %a" (sp_cast s p) e1 (sp_cast s p) e2
        | Compare(s, CLe, _) -> sp "%a <= %a" (sp_cast s p) e1 (sp_cast s p) e2
        | Compare(s, CGe, _) -> sp "%a >= %a" (sp_cast s p) e1 (sp_cast s p) e2
        | Sel _ -> sp "%a[%a]" pr e1 p0 e2
        | IndexedSlice (_, slice_sz) -> sp "%a[%a +: %d]" pr e1 p0 e2 slice_sz
        | And 1 ->  sp "%a && %a" p e1 p e2
        | And _ ->  sp "%a & %a" p e1 p e2
        | Or 1 -> sp "%a || %a" p e1 p e2
        | Or _ -> sp "%a | %a" p e1 p e2
        | Xor _ -> sp "%a ^ %a" p e1 p e2
        | Lsl (_, _) -> sp "%a << %a" p e1 p e2
        | Lsr (_, _) -> sp "%a >> %a" p e1 p e2
        | Asr (_, _) ->
           (* Arithmetic shifts need an explicit cast:
                reg [2:0] a     =        $signed(3'b100) >>> 1;                     // 3'b110
                reg [2:0] mux_a = 1'b1 ? $signed(3'b100) >>> 1 : 3'b000;            // 3'b010
                reg [2:0] b     =        $unsigned($signed(3'b100) >>> 1);          // 3'b110
                reg [2:0] mux_b = 1'b1 ? $unsigned($signed(3'b100) >>> 1) : 3'b000; // 3'b110
              (see https://stackoverflow.com/questions/60345469/) *)
           sp "%a" (sp_cast false sp_str) (sprintf "%a >>> %a" (sp_cast true p) e1 p e2)
        | EqBits (_, true) -> sp "%a != %a" p e1 p e2
        | EqBits (_, false) -> sp "%a == %a" p e1 p e2
        | Concat (_, _) -> sp "{%a, %a}" p0 e1 p0 e2
        | SliceSubst _ -> unlowered ())
    | EMux (s, e1, e2) -> sp "%a ? %a : %a" p s p e1 p e2
  and p_shared_entity out n =
    let p0 () n = snd (p_node out min_int n) in
    match n.entity with
    | Module { name; internal = true; inputs; outputs } ->
       let instance_name = gensym_next ("mod_" ^ name) in
       let outputs = List.map (fun op -> { op with op_wire = field_name instance_name op.op_wire }) outputs in
       let in_args = List.map (fun { ip_name; ip_node } -> sprintf ".%s(%a)" ip_name p0 ip_node) inputs in
       let out_args = List.map (fun { op_name; op_wire; _ } -> sprintf ".%s(%s)" op_name op_wire) outputs in
       let args = String.concat ", " (".CLK(CLK)" :: in_args @ out_args) in
       List.iter (fun { op_wire; op_sz; _ } -> p_decl out "wire" op_sz op_wire) outputs;
       p_stmt out 1 "%s %s(%s)" name instance_name args;
       instance_name
    | Module { name; internal = false; inputs; _ } ->
       List.iter (fun { ip_name; ip_node } ->
           p_assign out (field_name name ip_name) (p0 () ip_node))
         inputs;
       name
    | Expr e ->
       let _, s = p_wrapped_expr out min_int n.annots e in
       let name = name_node n in
       p_decl out "wire" n.size name ~expr:s;
       name
  and p_wrapped_expr out ctx_lvl annots expr =
    let lvl, s = p_expr out expr in
    let s = Debug.annotate annots s in
    if lvl <= ctx_lvl then (0, sprintf "(%s)" s) else (lvl, s)
  and p_shared_node out (n: node) =
    let name = p_shared_entity out n in
    n.kind <- Printed { name };
    (0, name)
  and p_node ?(restricted_ctx=false) out ctx_lvl (n: node) =
    match n.kind with
    | Shared -> p_shared_node out n
    | Printed { name } -> (0, name)
    | Unique ->
       match n.entity with
       | Module _ -> p_shared_node out n
       | Expr e -> if restricted_ctx && complex_expr e then p_shared_node out n
                   else p_wrapped_expr out ctx_lvl n.annots e

  let p_delayed out name expr =
    p_stmt out 3 "%s <= %s" name expr

  let p_root_init out roots =
    List.iter (fun (name, init, _) -> p_delayed out name (string_of_bits init)) roots

  let p_root_net out roots =
    List.iter (fun (name, _, net) -> p_delayed out name net) roots

  let p_always_block out roots =
    fprintf out "	always @(posedge CLK) begin\n";
    if omit_reset_line then
      p_root_net out roots
    else begin
        fprintf out "		if (!RST_N) begin\n";
        p_root_init out roots;
        fprintf out "		end else begin\n";
        p_root_net out roots;
        fprintf out "		end\n";
      end;
    fprintf out "	end\n"

  let p_root_network out (name, init, node) =
    (name, init, snd (p_node out min_int node))

  let p_root_decl out (name, init, _) =
    p_decl out "reg" (Array.length init) name ~expr:(string_of_bits init)

  let sp_pin (name, (direction, sz)) =
    let typ = sp_type (match direction with
                       | `Input -> "input wire"
                       | `Output -> "output wire") sz in
    sprintf "%s %s" typ name

  let p_header out modname ios =
    fprintf out "// -*- mode: verilog -*-\n";
    let pins = ("CLK", (`Input, 1)) :: ("RST_N", (`Input, 1)) :: ios in
    fprintf out "module %s(%s);\n" modname (String.concat ", " (List.map sp_pin pins))

  let p_module ~modname out { graph_roots; _ } =
    let metadata = compute_roots_metadata graph_roots in
    let roots, ios = translate_roots metadata graph_roots in
    p_header out modname (List.of_seq (Hashtbl.to_seq ios));
    List.iter (p_root_decl out) roots;
    fprintf out "\n";
    let root_exprs = List.map (p_root_network out) roots in
    fprintf out "\n";
    p_always_block out root_exprs;
    fprintf out "endmodule\n"
end

module Dot = struct
  let hd = "hd"

  let p_vertex out name args =
    let sp_arg (key, value) = sprintf "%s=\"%s\"" key value in
    let args = String.concat ", " (List.map sp_arg args) in
    fprintf out "%s [%s]\n" name args

  let p_edge out (n, f) (n', f') =
    fprintf out "%s:%s -> %s:%s\n" n f n' f'

  let name_of_tag tag =
    sprintf "N%d" tag

  type structure =
    | SInline of string
    | SVertex of string * (node * string) list

  let expr_structure (expr: expr) =
    match expr with
    | EPtr (n, None) -> SVertex ("ptr", [(n, hd)])
    | EPtr (n, Some s) -> SVertex ("ptr", [(n, s)])
    | EName nm -> SVertex (nm, [])
    | EConst cst -> SInline (string_of_bits cst)
    | EUnop (f, e1) -> SVertex (Debug.unop_to_str f, [(e1, hd)])
    | EBinop (f, e1, e2) -> SVertex (Debug.binop_to_str f, [(e1, hd); (e2, hd)])
    | EMux (s, e1, e2) -> SVertex ("mux", [(s, hd); (e1, hd); (e2, hd)])

  type result =
    | Named of string
    | Inlined of string

  let mark_visited node = function
    | Inlined _ -> ()
    | Named name -> node.kind <- Printed { name }

  let rec p_structure out name label args =
    let p_arg_label idx (n, n_port) =
      let port = sprintf "f%d" idx in
      let label_str = match p_node out n with
        | Named n_name -> p_edge out (n_name, n_port) (name, port); "."
        | Inlined s -> s in
      sprintf "<%s> %s" port label_str in
    let p_node_def name label args =
      let hd_label = sprintf "<hd> %s" label in
      let arg_labels = List.mapi p_arg_label args in
      let label = String.concat  "|" (hd_label :: arg_labels) in
      p_vertex out name [("label", label); ("shape", "record")] in
    p_node_def name label args;
    name
  and p_expr out tag e =
    match expr_structure e with
    | SInline s -> Inlined s
    | SVertex (label, args) -> Named (p_structure out (name_of_tag tag) label args)
  and p_node out (n: node) =
    match n.kind with
    | Unique | Shared ->
       let res = match n.entity with
         | Expr e -> p_expr out n.tag e
         | Module _ -> Named "FIXME" in
       mark_visited n res;
       res
    | Printed { name } -> Named name

  let p_root out (name, _, node) =
    ignore (p_structure out name name [(node, hd)])

  let p_module ~modname out { graph_roots; _ } =
    let metadata = compute_roots_metadata graph_roots in
    let roots, ios = translate_roots metadata graph_roots in
    fprintf out "digraph {\n";
    List.iter (p_root out) roots;
    fprintf out "}\n"

  let main target_dpath (modname: string) (c: circuit_graph) =
    with_output_to_file (Filename.concat target_dpath (modname ^ ".dot"))
      (p_module ~modname) c
end

let main target_dpath (modname: string) (c: circuit_graph) =
  with_output_to_file (Filename.concat target_dpath (modname ^ ".v"))
    (Verilog.p_module ~modname) c
