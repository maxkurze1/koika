(*! Frontend | Parser for the Kôika EDSL !*)
Require Import
  Koika.Common
  Koika.TypedSyntax
  Koika.IdentParsing
  Koika.SyntaxMacros.
Require Koika.Syntax. (* Necessary for scheduler *)
Require Import Unicode.Utf8.

Import Specif.SigTNotations.

Export Koika.Types.SigNotations.
Export Koika.Primitives.PrimTyped.
(* Export Koika.Primitives.PrimUntyped. *)
Export Coq.Strings.String.
Export Coq.Lists.List.ListNotations.

(**
 * This file defines the notations for the custom koika syntax.
 *)

Definition pos_t := unit.
Definition var_t := string.
Definition fn_name_t := string.
(* Koika *)
(* TODO: pos_t is set to unit just like in Frontent.v - does that make sense?  *)

Definition action'
  {tau sig reg_t ext_fn_t}
  (R : reg_t -> type)
  (Sigma: ext_fn_t -> ExternalSignature) :=
    (TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau).

Definition action
  {tau reg_t ext_fn_t}
  (R : reg_t -> type)
  (Sigma: ext_fn_t -> ExternalSignature) :=
    (TypedSyntax.action pos_t var_t fn_name_t R Sigma [] tau).

Definition function
  {tau sig reg_t ext_fn_t}
  (R : reg_t -> type)
  (Sigma: ext_fn_t -> ExternalSignature) :=
    Types.InternalFunction' fn_name_t
      (TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau).

Declare Custom Entry koika_t.

(* This is the entry point to transition from normal
  coq (constr) to koika *)
Notation "'<{' e '}>'" := (e) (e custom koika_t).

(* Koika_var *)
Declare Custom Entry koika_t_var.
Notation "a" := (ident_to_string a) (in custom koika_t_var at level 0, a ident, only parsing).
Notation "a" := (a) (in custom koika_t_var at level 0, a ident, format "'[' a ']'", only printing).

(* TODO better error messages *)
(* TODO explain why this class is necessary in the first place *)
Class VarRef {var_t} {tau : type} (k: var_t) sig := var_ref : member (k, tau) sig.
Hint Mode VarRef + - + + : typeclass_instances.
Arguments var_ref {var_t tau} k sig {VarRef} : assert.
Hint Extern 1 (VarRef ?k ?sig) => exact (projT2 (must (assoc k sig))) : typeclass_instances.

(* Koika_types *)
(* TODO improve arg list to be more consistent on nil case  *)
Declare Custom Entry koika_t_binder.
Notation "'(' x ':' y ')'" := (x%string, (y : type)) (in custom koika_t_binder at level 0, x custom koika_t_var, y constr).
Notation "a  ..  b" := (cons a ..  (cons b nil) ..)  (in custom koika_t_binder at level 1, a custom koika_t_binder at next level, b custom koika_t_binder at next level).


(* We want to tell the typechecker that the body of the function
 * should have the function's arguments in its context (sig).
 *
 * However, using a type hint where R Sigma are kept implicit
 * like:
 * ```
 * Definition some_act : action R Sigma :=
 * <{ ... }>: action' (sig := ...) _ _.
 * ```
 * does not work since coq is then trying to infer R and Sigma from
 * the body term instead of the outer definition.
 *
 * To tell coq to infer it from the definition we need
 * bidirectionality hints and thus we need a seperate function.
 *)
Local Definition refine_sig_tau sig tau {reg_t ext_fn_t}
  {R : reg_t -> type} {Sigma : ext_fn_t -> ExternalSignature}
  (a : action' R Sigma (tau := tau) (sig := sig)) : action' R Sigma := a.
Arguments refine_sig_tau sig tau & {reg_t ext_fn_t} {R Sigma} a : assert.

Notation "'fun' nm args ':' ret '=>' body" :=
  (Build_InternalFunction' nm%string (refine_sig_tau args ret body))
    (in custom koika_t at level 200, nm custom koika_t_var, args custom koika_t_binder, ret constr at level 0, right associativity, format "'[v' 'fun'  nm  args  ':'  ret  '=>' '/' body ']'").
Notation "'fun' nm '()' ':' ret '=>' body" :=
  (Build_InternalFunction' nm%string (refine_sig_tau nil ret body))
    (in custom koika_t at level 200, nm custom koika_t_var, ret constr at level 0, right associativity, format "'[v' 'fun'  nm  '()'   ':'  ret  '=>' '/' body ']'").

Notation "'assert' a 'in' c"          := (If a c (Const Ob)) (in custom koika_t at level 200, right associativity, format "'[v' 'assert'  a '/' 'in'  c ']'").
Notation "'assert' a 'else' b 'in' c" := (If a c b         ) (in custom koika_t at level 200, right associativity, format "'[v' 'assert'  a '/' 'else'  b '/' 'in'  c ']'").
Notation "'when' a 'do' t "           := (If a t (Const Ob)) (in custom koika_t at level 200, right associativity, format "'[v' 'when'  a '/' 'do'  t '/' ']'").

Notation "'let' a ':=' b 'in' c" := (Bind a b c) (in custom koika_t at level 200, a custom koika_t_var, right associativity, format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").
Notation "'let' a ':' typ ':=' b 'in' c" := (Bind (tau := typ) a b c) (in custom koika_t at level 200,
  a custom koika_t_var,
  typ constr at level 0, right associativity, format "'[v' 'let'  a  ':' typ ':='  b  'in' '/' c ']'").

Notation "a ';' b" := (Seq a                          b) (in custom koika_t at level 90, b at level 200, format "'[v' a ';' '/' b ']'" ).
Notation "a ';'"   := (Seq a (Const (tau := unit_t) Ob)) (in custom koika_t at level 90). (* trailing comma *)

Notation "'set' a ':=' b" := (Assign (var_ref a _) b) (in custom koika_t at level 89, a custom koika_t_var, only parsing).

Notation "'if' a 'then' t"            := (If a t                  (Const (tau := unit_t) Ob)) (in custom koika_t at level 89, t custom koika_t at level 89, right associativity, format "'[v' if  a '/' then  t ']'").
Notation "'if' a 'then' t 'else' f"   := (If a t                  f                         ) (in custom koika_t at level 89, t custom koika_t at level 89, right associativity, format "'[v' if  a '/' then  t '/' else  f ']'").
Notation "'guard' '(' a ')' "         := (If (Unop (Bits1 Not) a) (Fail (unit_t)) (Const Ob)) (in custom koika_t at level 89, right associativity, format "'guard' '(' a ')'").

(* Inspired by cpp the precedence  *)
(* https://en.cppreference.com/w/cpp/language/operator_precedence *)
(* TODO id really prefer to use || and && for logical operations and & | for bitwise *)
(* Bit operations *)
Notation "a  '||'  b"  := (Binop (Bits2 (Or       _))          a b) (in custom koika_t at level 85).
Notation "a  '^'  b"   := (Binop (Bits2 (Xor      _))          a b) (in custom koika_t at level 84).
Notation "a  '&&'  b"  := (Binop (Bits2 (And      _))          a b) (in custom koika_t at level 83).

(* Comparisons *)
Notation "a  '!='  b"  := (Binop (Eq _ true)                   a b) (in custom koika_t at level 80).
Notation "a  '=='  b"  := (Binop (Eq _ false)                  a b) (in custom koika_t at level 80).

Notation "a  '<'  b"   := (Binop (Bits2 (Compare false cLt _)) a b) (in custom koika_t at level 79).
Notation "a  '<s'  b"  := (Binop (Bits2 (Compare true  cLt _)) a b) (in custom koika_t at level 79).
Notation "a  '<='  b"  := (Binop (Bits2 (Compare false cLe _)) a b) (in custom koika_t at level 79).
Notation "a  '<s='  b" := (Binop (Bits2 (Compare true  cLe _)) a b) (in custom koika_t at level 79).
Notation "a  '>'  b"   := (Binop (Bits2 (Compare false cGt _)) a b) (in custom koika_t at level 79).
Notation "a  '>s'  b"  := (Binop (Bits2 (Compare true  cGt _)) a b) (in custom koika_t at level 79).
Notation "a  '>='  b"  := (Binop (Bits2 (Compare false cGe _)) a b) (in custom koika_t at level 79).
Notation "a  '>s='  b" := (Binop (Bits2 (Compare true  cGe _)) a b) (in custom koika_t at level 79).

(* Bit concatenation / shifts *)
Notation "a  '++'  b"  := (Binop (Bits2 (Concat _ _))          a b) (in custom koika_t at level 75).
Notation "a  '>>'  b"  := (Binop (Bits2 (Lsr _ _))             a b) (in custom koika_t at level 74).
Notation "a  '>>>'  b" := (Binop (Bits2 (Asr _ _))             a b) (in custom koika_t at level 74).
Notation "a  '<<'  b"  := (Binop (Bits2 (Lsl _ _))             a b) (in custom koika_t at level 74).

(* Arithmetic *)
Notation "a  '+'  b"   := (Binop (Bits2 (Plus     _))          a b) (in custom koika_t at level 70).
Notation "a  '-'  b"   := (Binop (Bits2 (Minus    _))          a b) (in custom koika_t at level 70).
Notation "a  '*'  b"   := (Binop (Bits2 (Mul    _ _))          a b) (in custom koika_t at level 69).

(* Unary operators *)
Notation "'!' a"       := (Unop  (Bits1 (Not _))               a  ) (in custom koika_t at level 65, format "'!' a").

Notation "a '[' b ']'"        := (Binop (Bits2 (Sel _))            a b) (in custom koika_t at level 60, format "'[' a [ b ] ']'").
Notation "a '[' b ':+' c ']'" := (Binop (Bits2 (IndexedSlice _ c)) a b) (in custom koika_t at level 60, c constr at level 0, format "'[' a [ b :+ c ] ']'").

(* get field of struct *)
(* Notation "a '.[' f ']'" := (UUnop (UStruct1 (UGetField f)) a) (in custom koika at level 60, f custom koika_var). *)

(* Section KoikaTypeCast.
  Context {reg_t ext_fn_t : Type}.
  Context {R : reg_t -> type}.
  Context {Sigma : ext_fn_t -> ExternalSignature}.
  (* #[local] Definition uaction := Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t. *)

  Class KoikaCast {sig} {tau_in} {tau_out}
    (v : action' (sig := sig) (tau := tau_in) R Sigma) := koika_cast : action' (sig := sig) (tau := tau_out) R Sigma.

  #[export] Instance koika_cast_struct {s v} : @KoikaCast _ (struct_sig s) _ v := (UUnop (UConv (UUnpack (struct_t s))) v).
  #[export] Instance koika_cast_enum   {s v} : @KoikaCast _ (enum_sig   s) _ v := (UUnop (UConv (UUnpack (enum_t s))) v).
  #[export] Instance koika_cast_arry   {s v} : @KoikaCast _ (array_sig  s) _ v := (UUnop (UConv (UUnpack (array_t s))) v).
End KoikaTypeCast. *)
(* since this syntax is untyped we dont know if expr
 * has a struct or bits type. However only bits can
 * be converted to structs using `UConv`. So this notations
 * is wrapping each expr in a `UPack` first to convert it
 * to bits and is then appliny the actual conversion to the
 * desired type.
 *)
(* Notation "expr : sig" :=
  (_ : KoikaCast sig (UUnop (UConv UPack) expr))
  (in custom koika at level 2, sig constr at level 0).

Notation "expr : 'bits' " :=
  (UUnop (UConv UPack) expr)
  (in custom koika at level 2). *)


Notation "'`' a '`'" := (a) (in custom koika_t, a constr).
Notation "'(' a ')'" := (a) (in custom koika_t, format "'[v' ( a ) ']'").

(* TODO does this really has to be `bits_t _` *)
(* TODO add support for enum and struct constants *)
Notation "'#' s" := (Const (tau := bits_t _) s) (in custom koika_t at level 0, s constr at level 0, only parsing).


(* ========================================================================= *)
(*                   Notations beginning with an identifier                  *)
(* ========================================================================= *)
(*
 * Note:
 *   All these notations need to be on the same level (here 0)
 *   else the parser would match on the highest level first and
 *   never even consider notations on a lower level.
 * 
 *   Likewise, all these notations need to start with a variable
 *   on the same level and in the same grammar (here a constr on level 0).
 *   Only so the parser can parse this variable first and then decide
 *   (depending on the following tokens) which notation matches.
 * 
 * Note:
 *   Some of the literal notations also start with an identifier.
 *   Thus, the same restrictions apply.
 *)
Notation "a" := (Var (var_ref (ident_to_string a) _)) (in custom koika_t at level 0, a constr at level 0, only parsing).
Notation "a" := (Var a) (in custom koika_t at level 0, a constr at level 0, only printing).

(* Alternative shorter set syntax
 * Note: expr is level 89 to stay below ';' *)
Export (hints) IdentParsing.TC.
Notation "a ':=' b" := (let aa := (TC.ident_to_string a) in Assign (var_ref aa _) b) (in custom koika_t at level 0, a constr at level 0, b custom koika_t at level 89, only parsing).
Notation "a ':=' b" := (                                    Assign a b             ) (in custom koika_t at level 0, a constr at level 0, b custom koika_t at level 89, only printing).

(*
 * Assume you have a function in a Modul:
 * ```
 * Inductive reg_t := reg1.
 * Definition R (r : reg_t) := bits_t 2.
 * Definition func : function R empty_Sigma := <{
 *   fun f () : bits_t 2 =>
 *     read0(reg1)
 * }>.
 * ```
 *
 * This function is typed using the [R] and [Sigma]
 * of the modul. However, to call this function in
 * a composition of modules it needs to be typed with
 * the [super_R] and (possibly) [super_Sigma] of this
 * larger module. (See TypedSyntax.v [InternalCall] -
 * `body` has the same R/Sigma as the retuned type)
 *
 * This function will lift a given action [act]
 *)
Fixpoint lift_reg
  {reg_t sreg_t ext_fn_t tau sig}
  {Sigma: ext_fn_t -> ExternalSignature}
  {R : forall r : reg_t, type}
  {sR : forall sr : sreg_t, type}
  (lift : {lift' : reg_t -> sreg_t | forall r : reg_t, sR (lift' r) = R r})
  (act : action' (tau := tau) (sig := sig) R Sigma)
  : action' (tau := tau) (sig := sig) sR Sigma :=
    let (lift_fn, liftH) := lift in
    match act with
    | Fail tau => Fail tau
    | Var mem => Var mem
    | Const val => Const val
    | Assign mem val => Assign mem (lift_reg lift val)
    | Seq a1 a2 => Seq (lift_reg lift a1) (lift_reg lift a2)
    | Bind var val body => Bind var (lift_reg lift val) (lift_reg lift body)
    | If cond tr fl => If (lift_reg lift cond) (lift_reg lift tr) (lift_reg lift fl)
    | Read port idx => rew liftH idx in
      Read port (lift_fn idx)
    | Write port idx val =>
      Write port (lift_fn idx) (lift_reg lift (rew <- liftH idx in val))
    | Unop fn arg => Unop fn (lift_reg lift arg)
    | Binop fn arg1 arg2 => Binop fn (lift_reg lift arg1) (lift_reg lift arg2)
    | ExternalCall fn arg => ExternalCall fn (lift_reg lift arg)
    | InternalCall fn args =>
      InternalCall {| int_name := fn.(int_name); int_body := (lift_reg lift fn.(int_body)) |}
      (rew List.map_id _ in @cmap _ _ _ (fun k_tau => action' (tau := (snd k_tau)) sR Sigma)
        id (fun _ => lift_reg lift) _ args)
    | APos pos a => APos pos (lift_reg lift a)
    end.

(* Koika_args *)
(* TODO support trailing comma *)
Declare Custom Entry koika_t_args.
Notation "'(' x ',' .. ',' y ')'" := (CtxCons (_,_) (x) .. (CtxCons (_,_) (y) CtxEmpty) ..) (in custom koika_t_args, x custom koika_t, y custom koika_t).
Notation "'(' ')'" := (CtxEmpty) (in custom koika_t_args).
Notation "'()'"    := (CtxEmpty) (in custom koika_t_args).

Notation "fn args" :=
  (InternalCall fn args)
    (in custom koika_t at level 0, fn constr at level 0, args custom koika_t_args, only parsing).

Notation "instance  '.(' fn ')' args" :=
  (InternalCall {| int_name := fn.(int_name); int_body := (lift_reg (exist _ instance (fun _ => eq_refl)) fn.(int_body)) |} args)
    (in custom koika_t at level 0, instance constr at level 0, fn constr, args custom koika_t_args).

Notation "'{' fn '}' args" :=
  (InternalCall fn args )
    (in custom koika_t at level 0, fn constr, args custom koika_t_args, only parsing).

(* ========================================================================= *)
(*                        Closed Notations on level 0                        *)
(* ========================================================================= *)

Notation "'pass'"  := (Const (tau := unit_t) Ob) (in custom koika_t).
(* the magic axiom can be used as value for an arbitrary type, use it with care *)
Require Magic.
Notation "'magic'" := (Magic.__magic__) (in custom koika_t).

Notation "'fail'"            := (Fail     unit_t) (in custom koika_t, format "'fail'").
Notation "'fail' '(' t ')'"  := (Fail (bits_t t)) (in custom koika_t, t constr, format "'fail' '(' t ')'").
Notation "'fail' '@(' t ')'" := (Fail          t) (in custom koika_t, t constr ,format "'fail' '@(' t ')'").

Notation "'read0' '(' reg ')' "           := (Read P0 reg)        (in custom koika_t, reg constr, format "'read0' '(' reg ')'").
Notation "'read1' '(' reg ')' "           := (Read P1 reg)        (in custom koika_t, reg constr, format "'read1' '(' reg ')'").
Notation "'write0' '(' reg ',' value ')'" := (Write P0 reg value) (in custom koika_t, reg constr, format "'write0' '(' reg ',' value ')'").
Notation "'write1' '(' reg ',' value ')'" := (Write P1 reg value) (in custom koika_t, reg constr, format "'write1' '(' reg ',' value ')'").

Notation "'zeroExtend(' a ',' b ')'" := (Unop (Bits1 (ZExtL _ b)) a) (in custom koika_t, b constr, format "'zeroExtend(' a ',' b ')'").
Notation "'sext(' a ',' b ')'"       := (Unop (Bits1 (SExt  _ b)) a) (in custom koika_t, b constr, format "'sext(' a ',' b ')'").

Notation "'ignore(' a ')'"           := (Unop (Conv _ Ignore)     a) (in custom koika_t).
Notation "'pack(' a ')'"             := (Unop (Conv _ Pack)       a) (in custom koika_t).
Notation "'unpack(' t ',' v ')'"     := (Unop (Conv t Unpack)     v) (in custom koika_t, t constr).

Notation "'extcall' method '(' arg ')'" := (ExternalCall method arg) (in custom koika_t, method constr at level 0).

(* for some reason, using struct_idx coq can infer the parameter
'sig' from the return type, by using StructIdx however, coq fails *)
(* Definition test : struct_index (Build_struct_sig' type "" [("foo", bits_t 1);("bar", bits_t 5)]) := struct_idx _ "foo". *)
(* Definition test' : struct_index (Build_struct_sig' type "" [("foo", bits_t 1);("bar", bits_t 5)]) := _ : StructIdx _ "foo". *)
Class StructIdx sig (f : string) := struct_idx : struct_index sig.
Hint Mode StructIdx + + : typeclass_instances.
Arguments struct_idx sig f {StructIdx} : assert.
Hint Extern 1 (StructIdx ?sig ?f) => exact (must (List_assoc f sig.(struct_fields))) : typeclass_instances.

Notation "'get' '(' v ',' f ')'" :=
  (Unop  (Struct1 GetField   _ (struct_idx _ f)) v)
  (in custom koika_t, f custom koika_t_var, format "'get' '(' v ','  f ')'").

Notation "'subst' '(' v ',' f ',' a ')'" :=
  (Binop (Struct2 SubstField _ (struct_idx _ f)) v a)
  (in custom koika_t, f custom koika_t_var, format "'subst' '(' v ','  f ',' a ')'").

Notation "'getbits@' sig '(' v ',' f ')'"          :=
  (Unop  (Bits1 (GetFieldBits   sig (must (List_assoc f sig.(struct_fields))))) v)
  (in custom koika_t, sig constr at level 0, f custom koika_t_var,
    format "'getbits@' sig '(' v ','  f ')'").
Notation "'substbits@' sig '(' v ',' f ',' a ')'"  :=
  (Binop (Bits2 (SubstFieldBits sig (must (List_assoc f sig.(struct_fields))))) v a)
  (in custom koika_t, sig constr at level 0, f custom koika_t_var,
    format "'substbits@' sig '(' v ','  f ','  a ')'").

(* TODO evaluate what this array feature should do and how far it is implemented *)
(* Notation "'aref' '(' v ',' f ')'"                   := (Unop  (Array1  (UGetElement         f)) v)   (in custom koika_t at level 1,                       v custom koika_t at level 13,                             f constr at level 0,           format "'aref' '(' v ','  f ')'").
Notation "'arefbits' '(' t ',' v ',' f ')'"         := (Unop  (Array1  (UGetElementBits   t f)) v)   (in custom koika_t at level 1, t constr at level 11, v custom koika_t at level 13,                             f constr at level 0,           format "'arefbits' '(' t ','  v ','  f ')'").
Notation "'asubst' '(' v ',' f ',' a ')'"           := (Binop (Array2  (USubstElement       f)) v a) (in custom koika_t at level 1,                       v custom koika_t at level 13, a custom koika_t at level 13, f constr at level 0,           format "'asubst' '(' v ','  f ',' a ')'").
Notation "'asubstbits' '(' t ',' v ',' f ',' a ')'" := (Binop (Array2  (USubstElementBits t f)) v a) (in custom koika_t at level 1, t constr at level 11, v custom koika_t at level 13, a custom koika_t at level 13, f constr at level 0,           format "'asubstbits' '(' t ','  v ','  f ',' a ')'").  *)

(* Koika_branches *)
Declare Custom Entry koika_t_branches.
Notation "x '=>' a"      := [(x,a)]        (in custom koika_t_branches at level 0, x custom koika_t at level 200, a custom koika_t at level 200).
Notation "arg1 '|' arg2" := (arg1 ++ arg2) (in custom koika_t_branches at level 1, format "'[v' arg1 ']' '/' '|'  '[v' arg2 ']'").

(* TODO total match -> maybe for enums? *)
(* For example if var has enum type then allow special match with 
member names instead of `type::<mem>` and with optional default case

*)
Fixpoint macro_switch
  {reg_t ext_fn_t} {R: reg_t -> type} {Sigma: ext_fn_t -> ExternalSignature}
  {sig tau tau_eq}
  (var: action' (tau := tau_eq) R Sigma)
  (default: action' (tau := tau) R Sigma)
  (branches: list (action' (tau := tau_eq) R Sigma * action' (tau := tau) (sig := sig) R Sigma))
    : action' (tau := tau) (sig := sig) R Sigma :=
  match branches with
  | nil => default
  | (label, act) :: branches =>
    If (Binop (Eq _ false) var label) act (macro_switch var default branches)
  end.
Notation "'match' var 'with' '|' branches 'return' 'default' ':' default 'end'" :=
  (macro_switch var default branches)
    (in custom koika_t, branches custom koika_t_branches,
      format "match  var  with '/' '[v'  |  branches '/' return  default :  default ']' end").

(* ========================================================================= *)
(*                                  Literals                                 *)
(* ========================================================================= *)

(* Koika_consts *)
Declare Custom Entry koika_t_consts.
Notation "'1'" := (Ob~1) (in custom koika_t_consts at level 0).
Notation "'0'" := (Ob~0) (in custom koika_t_consts at level 0).
Notation "bs '~' '0'" := (Bits.cons false bs) (in custom koika_t_consts at level 1, left associativity, format "bs '~' '0'").
Notation "bs '~' '1'" := (Bits.cons  true bs) (in custom koika_t_consts at level 1, left associativity, format "bs '~' '1'").

Notation "'Ob' '~' number" := (Const (tau := bits_t _) number)
  (in custom koika_t at level 0, number custom koika_t_consts, format "'Ob' '~' number").
Notation "'Ob'" := (Const (tau := bits_t 0) Ob)
  (in custom koika_t at level 0, format "'Ob'").

(* koika bit vector literals *)
(* From Coq Require BinaryString OctalString HexString HexadecimalString DecimalString.

(* Coq's implementation just silently returns 0 on an invalid string -
  for better error recognition these methods are redefined here returning option *)
Local Fixpoint num_string_to_option_N' (s : string) (base : N) (convert : Ascii.ascii -> option N) (remainder : option N) : option N :=
  match s with
  | EmptyString => remainder
  | String c s' => num_string_to_option_N' s' base convert
    (match remainder, convert c with
    | Some rem, Some c_v => Some (N.add (N.mul base rem) c_v)
    | _, _ => None
    end)
  end.
Local Definition num_string_to_option_N (s : string) (base : N) (convert : Ascii.ascii -> option N) : option N :=
  match s with
  | EmptyString => None
  | String _ _ => num_string_to_option_N' s base convert (Some 0%N)
  end.

Local Definition bin_string_to_N s := (must (num_string_to_option_N s 2 BinaryString.ascii_to_digit)).
Local Definition oct_string_to_N s := (must (num_string_to_option_N s 8 OctalString.ascii_to_digit)).
Local Definition dec_string_to_N s := (must (option_map N.of_uint (DecimalString.NilZero.uint_of_string s))).
Local Definition hex_string_to_N s := (must (num_string_to_option_N s 16 HexString.ascii_to_digit)). *)

Local Definition len := String.length.

(* Bits.of_N with an inferred length or a default if inference fails *)
Ltac bits_of_N default val :=
  exact (Bits.of_N default val) + exact (Bits.of_N _ val).
  (* match goal with
  | |- bits ?n =>
    tryif has_evar n
    then exact (Bits.of_N default val)
    else exact (Bits.of_N _ val)
  end. *)

Notation "num ':b' sz" := (Const (tau := bits_t _)      (Bits.of_N (sz <: nat)            (bin_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':b'"    := (Const (tau := bits_t _) ltac:(bits_of_N ((len num) * 1)        (bin_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0b' num sz" := (Const (tau := bits_t _)      (Bits.of_N (sz <: nat)            (bin_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, format "'0b' num sz").
Notation "'0b' num"    := (Const (tau := bits_t _) ltac:(bits_of_N ((len num) * 1)        (bin_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0b' num"    := (Const (tau := bits_t _)      (Bits.of_N _                      (bin_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, only printing,        format "'0b' num").

Notation "num ':o' sz" := (Const (tau := bits_t _)      (Bits.of_N (sz <: nat)            (oct_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':o'"    := (Const (tau := bits_t _) ltac:(bits_of_N ((len num) * 3)        (oct_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0o' num sz" := (Const (tau := bits_t _)      (Bits.of_N (sz <: nat)            (oct_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, format "'0o' num sz").
Notation "'0o' num"    := (Const (tau := bits_t _) ltac:(bits_of_N ((len num) * 3)        (oct_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0o' num"    := (Const (tau := bits_t _)      (Bits.of_N _                      (oct_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, only printing,        format "'0o' num").

Notation "num ':d' sz" := (Const (tau := bits_t _)      (Bits.of_N (sz <: nat)            (dec_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':d'"    := (Const (tau := bits_t _) ltac:(bits_of_N (1 + (N.to_nat (N.log2 (dec_string_to_N num))))
                                                                                          (dec_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0d' num sz" := (Const (tau := bits_t _)      (Bits.of_N (sz <: nat)            (dec_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, format "'0d' num sz").
Notation "'0d' num"    := (Const (tau := bits_t _) ltac:(bits_of_N (1 + (N.to_nat (N.log2 (dec_string_to_N num))))
                                                                                          (dec_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0d' num"    := (Const (tau := bits_t _)      (Bits.of_N _                      (dec_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, only printing,        format "'0d' num").

Notation "num ':h' sz" := (Const (tau := bits_t _)      (Bits.of_N (sz <: nat)            (hex_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':h'"    := (Const (tau := bits_t _) ltac:(bits_of_N ((len num) * 4)        (hex_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0x' num sz" := (Const (tau := bits_t _)      (Bits.of_N (sz <: nat)            (hex_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, format "'0x' num sz").
Notation "'0x' num"    := (Const (tau := bits_t _) ltac:(bits_of_N ((len num) * 4)        (hex_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0x' num"    := (Const (tau := bits_t _)      (Bits.of_N _                      (hex_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, only printing,        format "'0x' num").


(* legacy number format *)
Notation "'|' a '`d' b '|'" := (Const (tau := bits_t _) (Bits.of_N (a<:nat) b%N)) (in custom koika_t at level 0, a constr at level 0, b constr at level 0).

(* literal inside koika - wrapped inside Const to function as a uaction *)
(* Notation "'|' literal '|'" := (Const (tau := bits_t _) literal) (in custom koika_t, literal custom koika_t_literal). *)

(* ========================================================================= *)
(*                                Constructors                               *)
(* ========================================================================= *)

Section Macro.
  Context {reg_t ext_fn_t: Type}.
  Context {R : reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  (* A koika action which build a struct instance filled 
  with zeroes *)
  Definition struct_init_zeros {sig} (tau: type) : action' (sig := sig) R Sigma :=
    Unop (Conv tau Unpack) (Const (tau := bits_t _) (Bits.zeroes (type_sz tau))).

  (* Transforming a list of actions into a sequence of
  substitute operations to initialize a struct *)
  Fixpoint struct_init {sig} (s_sig: struct_sig)
    (fields: list {idx : struct_index s_sig & (action' (tau := field_type s_sig idx) (sig := sig) R Sigma)})
    : action' (sig := sig) R Sigma :=
    match fields with
    | (idx;act) :: fields' =>
      (Binop (Struct2 SubstField s_sig idx)) (struct_init s_sig fields') act
    | [] => struct_init_zeros (struct_t s_sig)
    end.

  (* The struct's signature needs to be known to check if a given field exists within
  the struct and to compute its index.

  This signature is inferred by the typechecker when the notation is used. This typeclass
  makes sure that the index computation is deferred and only executed after the signature
  is known *)
  Class FieldSubst {tau sig} (s_sig : struct_sig) (field : string) (a : action' (sig := sig) (tau := tau) R Sigma) :=
    field_subst : {idx : struct_index s_sig & (action' (sig := sig) (tau := field_type s_sig idx) R Sigma )}.

End Macro.
Hint Mode FieldSubst + + + + + + + + + : typeclass_instances.
Arguments field_subst {reg_t ext_fn_t} {R Sigma} {tau sig} s_sig field a {FieldSubst} : assert.
Hint Extern 1 (FieldSubst ?sig ?field ?a) => exact ((must (List_assoc field sig.(struct_fields)) ; a)) : typeclass_instances.

Declare Custom Entry koika_t_struct.
Declare Custom Entry koika_t_struct_field.
(* struct instantiation in koika *)
(* expr at level at level 89 to stay below koika's sequence (a ; b) *)
Notation "f ':=' expr" := (field_subst _ f expr)
  (in custom koika_t_struct_field at level 0, f custom koika_t_var, expr custom koika_t at level 89).
Notation "a ';' b" := (cons a b)   (in custom koika_t_struct at level 0, a custom koika_t_struct_field, right associativity).
Notation "a ';'"   := (cons a nil) (in custom koika_t_struct at level 0, a custom koika_t_struct_field). (* trailing comma *)
Notation "a"       := (cons a nil) (in custom koika_t_struct at level 0, a custom koika_t_struct_field).


Notation "'struct' sig '::{' '}'" :=
  (struct_init sig []) (in custom koika_t, sig constr at level 0).

Notation "'struct' sig '::{' fields '}'" :=
  (struct_init sig fields) (in custom koika_t, sig constr at level 0,
  fields custom koika_t_struct).

(* Needs the same level as 'Var' + level of first non-terminal must match *)
Notation "sig '::{' '}'" :=
  (struct_init sig []) (in custom koika_t at level 0, sig constr at level 0).

Notation "sig '::{' fields '}'" :=
  (struct_init sig fields) (in custom koika_t at level 0, sig constr at level 0,
  fields custom koika_t_struct).

Notation "'enum' sig '::<' f '>'" :=
  (Const (tau := enum_t sig) (vect_nth sig.(enum_bitpatterns) (must (vect_index f sig.(enum_members)))))
    (in custom koika_t, sig constr at level 0, f custom koika_t_var).
(* shorter syntax to omit 'enum' keyword *)
(* Needs the same level as 'Var' + level of first non-terminal must match *)
Notation "sig '::<' f '>'" :=
  (Const (tau := enum_t sig) (vect_nth sig.(enum_bitpatterns) (must (vect_index f sig.(enum_members)))))
    (in custom koika_t at level 0, sig constr at level 0, f custom koika_t_var).


(* ========================================================================= *)
(*                            scheduler notations                            *)
(* ========================================================================= *)

(* scheduler *)
(* TODO rather use custom grammar for scheduler *)
Notation "r '|>' s" :=
  (Syntax.Cons r s)
    (at level 99, s at level 99, right associativity).
Notation "'done'" :=
  Syntax.Done (at level 99).



Module TODO_contrs_arg_lists.

  Arguments CtxCons {K V} {sig} k & v ctx.
  Definition test : context (fun x => type_denote (snd x)) [("fst", bits_t 3)]
    := CtxCons _ (Bits.of_nat 3 2) (CtxEmpty).

  Notation "'::(' x ',' .. ',' y ')'" := (CtxCons _ (x) .. (CtxCons _ (y) CtxEmpty) ..).

End TODO_contrs_arg_lists.

(* ========================================================================= *)
(*                          Bidirectionality hints                           *)
(* ========================================================================= *)
(* These hints are very helpful for the type checker.
 * These hints tell it to first infer R, Sigma and sig which are passed from
 * the outer terms into the inner terms and then they are used to infer the
 * type of registers and variables.                                          *)

Arguments Fail         {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig} & tau : assert.
Arguments Var          {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig} & {k tau} m : assert.
Arguments Const        {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig tau} & cst : assert.
Arguments Assign       {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig} & {k tau} m ex : assert.
Arguments Seq          {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig tau} & r1 r2 : assert.
Arguments Bind         {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig tau} & {tau'} var ex body : assert.
Arguments If           {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig tau} & cond tbranch fbranch : assert.
Arguments Read         {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig} port idx & : assert.
Arguments Write        {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig} port idx & value : assert.
Arguments Unop         {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig} fn & arg1 : assert.
Arguments Binop        {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig} fn & arg1 arg2 : assert.
Arguments ExternalCall {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig} & fn arg : assert.
Arguments InternalCall {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig tau} {argspec} & fn args : assert.
Arguments APos         {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma} {sig tau} & pos a : assert.
Arguments Build_InternalFunction' {fn_name_t action} & int_name int_body : assert.
Arguments macro_switch {reg_t ext_fn_t} {R Sigma} {sig} & {tau tau_eq} var default branches : assert.
Arguments struct_init {reg_t ext_fn_t} {R Sigma} {sig} & s_sig fields : assert.

(* ========================================================================= *)
(*                                   Tests                                   *)
(* ========================================================================= *)

Module Tests'.
Section Tests'.
  Inductive reg_t :=
  | reg0
  | reg1.

  Definition R (r : reg_t) := bits_t 64.
  Definition R' (r : reg_t) :=
    match r with
    | reg0 => bits_t 64
    | reg1 => bits_t 64
    end.

  Context {ext_fn_t : Type}.
  Context {Sigma : ext_fn_t -> ExternalSignature}.

  Definition read_reg : function R Sigma := <{
  fun read_reg (select : bits_t 1) : bits_t 64 =>
    let data :=
      if select
      then read0(reg1)
      else read0(reg0)
    in data
  }>.

  Definition read_reg' : function R' Sigma := <{
  fun read_reg' (select : bits_t 1) : bits_t 64 =>
    if select
      then read0(reg1)
      else read0(reg0)
  }>.

  Inductive ext_fn_t' :=
  | ext1.
  Definition Sigma' (fn: ext_fn_t') := {$ bits_t 1 ~> bits_t 64 $}.

  Definition get_data' : action' R Sigma' (sig := [("select", bits_t 1)]) := <{
    if select
      then extcall ext1(Ob~1)
      else read0(reg1)
  }>.

  Definition get_data : function R Sigma' := <{
  fun get_data (select : bits_t 1) : bits_t 64 =>
    if select
      then extcall ext1(Ob~1)
      else read0(reg1)
  }>.
End Tests'.
End Tests'.

Module Type Tests.
  Inductive reg_t := reg1.
  Parameter ext_fn_t : Type.
  Definition R (r : reg_t) : type := bits_t 2.
  Parameter Sigma: ext_fn_t -> ExternalSignature.

  Notation _action := (action R Sigma).

  Definition test_num : _action := <{ Ob~1~1~1 }>.
  Definition test_lit  : _action := <{ Ob~1~1~0~0~1 }>.
  Definition test_lit2 : _action := <{ |10 `d 10| }>.
  Definition test_pass : _action := <{ pass }>.

  Definition test_var    : _action := <{ let a := Ob~1~1 in a }>.
  Definition test_seq    : _action := <{ let a := Ob~1~1 in pass; a }>.
  Definition test_assign : _action := <{ let a := Ob~1~1 in a := Ob~0~1 }>.

  Definition numbers_e := {|
    enum_name        := "some_enum_name";
    enum_members     :=                          [ "ONE"; "TWO"; "THREE"; "IDK" ];
    enum_bitpatterns := vect_map (Bits.of_nat 3) [ 1    ; 2    ; 3      ; 7     ]
  |}%vect.

  Definition test_enum : _action := <{
    enum numbers_e::<ONE>
  }>.

  Definition func : function R Sigma := <{
    fun f () : bits_t 2 =>
      read0(reg1)
  }>.

  Inductive reg_t_super := sreg1 (r : reg_t).
  Definition super_R (sr : reg_t_super) := match sr with
    | sreg1 r => R r
    end.

  Definition super_func : function super_R Sigma := <{
    fun sup_f () : bits_t 2 =>
      sreg1.(func)()
  }>.

  Definition test_func2 : function R Sigma := <{
    fun f (arg1 : bits_t 1) (arg2 : bits_t 3) : bits_t 2 =>
      read0(reg1)
  }>.

  Definition test_funcall : function R Sigma := <{
    fun f () : bits_t 2 =>
      test_func2(0b"1", 0b"011")
  }>.

  Definition numbers_s := {|
    struct_name := "numbers";
    struct_fields := [
      ("one"  , bits_t 3);
      ("two"  , bits_t 3);
      ("three", bits_t 3)
    ];
  |}.

  Definition test_struct_init : _action := <{
    struct numbers_s::{
      one := Ob~1~1~1;
      two := Ob~1~1~1
    }
  }>.

  Definition test_struct_init_trailing_comma : _action := <{
    struct numbers_s::{
      two   := "100":b;
      three := "101":b;
    }
  }>.
  Definition test_struct_init_empty : _action := <{
    struct numbers_s::{ }
  }>.
End Tests.
Module Type Tests2.
  Inductive reg_t :=
  | data0 | data1.
  Definition R (r : reg_t) := bits_t 5.
  Parameter ext_fn_t : Type.
  Parameter Sigma: ext_fn_t -> ExternalSignature.
  Definition _action {tau} := action (tau := tau) R Sigma.
  Definition test_2 : _action := <{ Ob~1~1 }>.
  Definition test_bits : _action := <{ 0b"010" }>.
  Definition test_1 : _action := <{ let yoyo := fail(2) in pass }>.
  Definition test_1' : _action := <{ let yoyo := fail(2) in yoyo }>.
  Definition test_2' : _action := <{ pass; pass }>.
  Definition test_set : _action := <{ let yoyo := Ob~1~1~0~0~1 in set yoyo := read0(data0) ; pass }>.
  Definition test_noset : _action := <{ let yoyo := pass in yoyo := pass ; pass }>.
  Fail Definition test_3'' : _action := <{ set yoyo := pass ; pass }>.
  Fail Definition test_5 : _action := <{ let yoyo := set yoyo := pass in pass }>.
  Inductive test := rData (n:nat).
  Definition test_R (r : test) := bits_t 5.
  Definition test_9 : _action := <{ read0(data0) }>.
  Definition test_10 : nat -> action test_R Sigma := (fun idx => <{ read0(rData idx) }>).
  Definition test_11 : _action := <{ (let yoyo := read0(data0) in write0(data0, Ob~1~1~1~1~1)); fail }>.
  Fail Definition test_11' : _action := <{ (let yoyo := read0(data0) in write0(data0, Ob~1~1~1~1)); fail }>.
  Definition test_12 : _action := <{ (let yoyo := if fail (1) then read0(data0) else fail (5) in write0(data0, 0b"01100")); fail }>.
  Fail Definition test_13 : _action := <{ yoyo }>.
  Definition test_14 : _action := <{ !Ob~1 && Ob~1 }>.
  Definition test_14' : _action := <{ !(Ob~1 && Ob~1) }>.
  Example eq : test_14 <> test_14'. compute; congruence. Defined.
  Definition test_15 : _action := <{ 0b"10011" && read0(data0) }>.
  Definition test_16 : _action := <{ !read0(data1) && !read0(data1) }>.
  Definition test_lit : _action (tau := bits_t 5) := (Seq (Write P0 data0 <{ Ob~1~1~0~0~1 }>) (Const (tau := bits_t _) (Bits.of_N ltac:(let x := eval cbv in ((len "01100") * 1) in exact x) (bin_string_to_N "01100")))).
  Definition test_20 : _action := <{ (0b"11001100")[ Ob~0~0~0 :+ 3 ] }>.
  Definition test_23 : function R Sigma := <{ fun test (arg1 : (bits_t 3)) (arg2 : bits_t 2) : bits_t 4 => fail @(_) }>.
  Definition test_24 (sz : nat) : function R Sigma := <{ fun test (arg1 : bits_t sz) (arg1 : bits_t sz) : bits_t sz  => fail(sz)}>.
  Definition test_25 (sz : nat) : function R Sigma := <{ fun test (arg1 : bits_t sz ) : bits_t sz => let oo := fail(sz) >> fail(sz) in oo}>.
  Definition test_26 (sz : nat) : function R Sigma := <{ fun test () : bits_t sz  => fail(sz) }>.
  Definition test_write : _action := <{ write0(data0, 0b"01101") }>.

  Definition min {reg_t ext_fn_t : Type} {R : reg_t -> type}
    {Sigma : ext_fn_t -> ExternalSignature}
    (bit_size : nat) : function R Sigma := <{
    fun min (first: bits_t bit_size) (second: bits_t bit_size) : bits_t bit_size =>
      if first < second then first else second
    }>.

  Definition idk : _action := <{
    (!read0(data0))[Ob~1~1~1 :+ 3]
  }>.
  
  Definition idk2 : _action := <{
    let idk := Ob~1~1~1~0~0 in
    ignore(if (!idk)[#(Bits.of_nat 3 0) :+ 1] then (
        write0(data0, 0b"01101");
        pass
      ) else pass);
    fail
  }>.
  Program Definition test_27 : _action := <{
    ignore(if (!read0(data0))[#(Bits.of_nat _ 0) :+ 1] then (
      write0(data0, 0b"01101");
      let yo := if (Ob~1) then 0b"1001" else 0x"F" in
      write0(data0, yo ++ Ob~1);
      0b"00011"5
      ) else read0(data0));
    fail
  }>.
  Fail Next Obligation.
  Definition test_28 : _action :=  <{
    let var := 0b"101" in
    match var with
    | Ob~1~1~1 => pass
    | Ob~0~1~1 => pass
    return default: pass
    end
  }>.

  Definition mem_req :=
    {| struct_name := "mem_req";
       struct_fields := [("foo", bits_t 2); ("bar", bits_t 32)] |}.

  Definition test_30'' : _action := <{
    let upu := 0x"C0" in
    struct mem_req::{ foo := upu[#(Bits.of_nat _ 0) :+ 2] ;
                      bar := "98":d32 }
  }>.

  Definition test_31' : _action := <{
    let upu := 0x"C0" in
    let a := struct mem_req::{ foo := upu[0x"0" :+ 2] ;
                               bar := |32`d98| } in
      unpack(struct_t mem_req, pack(a))
  }>.
  
  (* Accessing enum constants *)
  Definition some_s := {|
    struct_name:= "some_s";
    struct_fields :=
    [ ("one"  , bits_t 3);
      ("two"  , bits_t 3) ]
  |}.

  Program Definition test_get : function R Sigma := <{
    fun idk (num : struct_t some_s) : bits_t 3 =>
      get(num, one)
  }>.
  Fail Next Obligation.

  Program Definition test_subst : function R Sigma := <{
    fun idk (num : struct_t some_s) : struct_t some_s =>
      subst(num, one, Ob~1~0~0)
  }>.
  Fail Next Obligation.
  
  Notation "'[|' a '=koika=' b '|]'" := ((a : _action) = (b : _action)) (a custom koika_t, b custom koika_t).

  (* sequences in match statements without paranthesis *)
  Definition test_32 : [|
    let x := 0x"C0"5 in
    match |5`d10| with
    | |5`d10| => (
      write0(data0, x);
      x
    )
    | |5`d 9| => (
      x
    )
    return default: fail (5)
    end
  =koika=
    let x := 0x"C0"5 in
    match |5`d10| with
    | |5`d10| =>
      write0(data0, x);
      x
    | |5`d 9| =>
      x
    return default: fail (5)
    end
  |] := eq_refl.

  (* else branch takes single instruction from sequence *)
  Definition test_33 : [|
    if Ob~1
      then pass
      else pass;
    pass
  =koika=
    (if Ob~1
      then pass
      else pass);
    pass
  |] := eq_refl.

  (* if' then branch takes single instruction from sequence *)
  Definition test_34 : [|
    if Ob~1
      then pass;
    pass
  =koika=
    (if Ob~1 then
      pass);
    pass
  |] := eq_refl.

  Definition numbers_e := {|
    enum_name        := "some_enum_name";
    enum_members     :=                          [ "ONE"; "TWO"; "THREE"; "IDK" ];
    enum_bitpatterns := vect_map (Bits.of_nat 3) [ 1    ; 2    ; 3      ; 7     ]
  |}%vect.

  (* Accessing enum constants *)
  Definition numbers_s := {|
    struct_name:= "some_s";
    struct_fields :=
    [ ("one"  , bits_t 3);
      ("two"  , bits_t 3);
      ("three", bits_t 3);
      ("four" , bits_t 3);
      ("five" , enum_t numbers_e) ]
  |}.
 
  Definition num_test_b_1 : [| "01101":b     =koika= Ob~0~1~1~0~1 |] := eq_refl.
  Definition num_test_b_2 : [| 0b"00011"     =koika= Ob~0~0~0~1~1 |] := eq_refl.
  Definition num_test_b_3 : [| "11":b5       =koika= Ob~0~0~0~1~1 |] := eq_refl.
  Definition num_test_b_4 : [| 0b"10"5       =koika= Ob~0~0~0~1~0 |] := eq_refl.
  Definition num_test_b_5 : [| 0b"10010110"3 =koika= Ob~1~1~0     |] := eq_refl.
  Fail Definition num_test_b_6  := <{ 0b"102"  }> : _action.
  Fail Definition num_test_b_7  := <{ 0b"10f"6 }> : _action.
  Fail Definition num_test_b_8  := <{ "f0":b5  }> : _action.
  Fail Definition num_test_b_9  := <{ "f0":b   }> : _action.
  Fail Definition num_test_b_10 := <{ "":b     }> : _action.

  Definition num_test_o_1 : [| "330":o   =koika= Ob~0~1~1~0~1~1~0~0~0     |] := eq_refl.
  Definition num_test_o_2 : [| "070":o9  =koika= Ob~0~0~0~1~1~1~0~0~0     |] := eq_refl.
  Definition num_test_o_3 : [| 0o"000"   =koika= Ob~0~0~0~0~0~0~0~0~0     |] := eq_refl.
  Definition num_test_o_4 : [| 0o"750"11 =koika= Ob~0~0~1~1~1~1~0~1~0~0~0 |] := eq_refl.
  Definition num_test_o_5 : [| 0o"751"3  =koika= Ob~0~0~1                 |] := eq_refl.
  Fail Definition num_test_o_6  := <{ 0o"108"   }> : _action.
  Fail Definition num_test_o_7  := <{ 0o"080"10 }> : _action.
  Fail Definition num_test_o_8  := <{ "f00":o10 }> : _action.
  Fail Definition num_test_o_9  := <{ "00f":o5  }> : _action.
  Fail Definition num_test_o_10 := <{ "":o      }> : _action.

  Definition num_test_d_1 : [| "33":d    =koika= Ob~1~0~0~0~0~1           |] := eq_refl.
  Definition num_test_d_2 : [| "33":d9   =koika= Ob~0~0~0~1~0~0~0~0~1     |] := eq_refl.
  Definition num_test_d_3 : [| "070":d9  =koika= Ob~0~0~1~0~0~0~1~1~0     |] := eq_refl.
  Definition num_test_d_4 : [| 0d"070"   =koika= Ob~1~0~0~0~1~1~0         |] := eq_refl.
  Definition num_test_d_5 : [| 0d"198"11 =koika= Ob~0~0~0~1~1~0~0~0~1~1~0 |] := eq_refl.
  Definition num_test_d_6 : [| 0d"15"3   =koika= Ob~1~1~1                 |] := eq_refl.
  Fail Definition num_test_d_7  := <{ 0d"1a0"   }> : _action.
  Fail Definition num_test_d_8  := <{ 0d"0z0"10 }> : _action.
  Fail Definition num_test_d_9  := <{ "f00":d10 }> : _action.
  Fail Definition num_test_d_10 := <{ "00f":d5  }> : _action.
  Fail Definition num_test_d_11 := <{ "":d      }> : _action.

  Definition num_test_h_1 : [| "fa":h    =koika= Ob~1~1~1~1~1~0~1~0         |] := eq_refl.
  Definition num_test_h_2 : [| "bb":h9   =koika= Ob~0~1~0~1~1~1~0~1~1       |] := eq_refl.
  Definition num_test_h_3 : [| "014":h   =koika= Ob~0~0~0~0~0~0~0~1~0~1~0~0 |] := eq_refl.
  Definition num_test_h_4 : [| 0x"070"   =koika= Ob~0~0~0~0~0~1~1~1~0~0~0~0 |] := eq_refl.
  Definition num_test_h_5 : [| 0x"198"11 =koika= Ob~0~0~1~1~0~0~1~1~0~0~0   |] := eq_refl.
  Definition num_test_h_6 : [| 0x"1d"3   =koika= Ob~1~0~1                   |] := eq_refl.
  Fail Definition num_test_h_7  := <{ 0x"1h0"   }> : _action.
  Fail Definition num_test_h_8  := <{ 0x"0z0"10 }> : _action.
  Fail Definition num_test_h_9  := <{ "g00":h10 }> : _action.
  Fail Definition num_test_h_10 := <{ "00k":h5  }> : _action.
  Fail Definition num_test_h_11 := <{ "":h      }> : _action.
End Tests2.
