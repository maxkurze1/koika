Require Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import
        Koika.Syntax
        Koika.IdentParsing.

Export Koika.Types.SigNotations.
Export Koika.Primitives.PrimUntyped.
Export Coq.Strings.String.
Export Coq.Lists.List.ListNotations.

Open Scope list_scope.
Open Scope string_scope.

Declare Custom Entry koika.
Declare Custom Entry koika_args.
Declare Custom Entry koika_var.
Declare Custom Entry koika_types.
Declare Custom Entry koika_branches.
Declare Custom Entry koika_consts.

(* Koika_consts *)
Notation "bs1 '~' bs2" :=
  (Bits.app bs2 bs1)
    (in custom koika_consts at level 7, right associativity, format "bs1 '~' bs2").
Notation "'1'" :=
  (Bits.ones 1)
    (in custom koika_consts at level 0).
Notation "'0'" :=
  (Bits.zeroes 1)
    (in custom koika_consts at level 0).
Notation "'Ob' ~ number" :=
  (USugar (UConstBits number))
    (in custom koika at level 7, number custom koika_consts at level 99, format "'Ob' '~' number").

Notation "'|' a '`d' b '|'" :=
  (USugar (UConstBits (Bits.of_N (a<:nat) b%N)))
    (in custom koika, a constr at level 0 , b constr at level 0).

(* Koika_args *)
Declare Custom Entry koika_middle_args.
Notation "x" := [x] (in custom koika_middle_args at level 0, x custom koika at level 99).
Notation "x ',' y" := (app x y) (in custom koika_middle_args at level 1, x custom koika_middle_args, y custom koika_middle_args, right associativity).

Notation "'()'"  := nil (in custom koika_args).
Notation "'( )'"  := nil (in custom koika_args).
Notation "'(' x ')'"  := x (in custom koika_args, x custom koika_middle_args).

(* Koika_var *)
Notation "a" := (ident_to_string a) (in custom koika_var at level 0, a constr at level 0, format "'[' a ']'",only parsing).
Notation "a" := (a) (in custom koika_var at level 0, a constr at level 0, format "'[' a ']'",only printing).

(* Koika_types *)
Notation " '(' x ':' y ')'" := (cons (prod_of_argsig {| arg_name := x%string; arg_type := y |}) nil) (in custom koika_types at level 60, x custom koika_var at level 0, y constr at level 12 ).
Notation "a  b" := (app a b)  (in custom koika_types at level 95, a custom koika_types , b custom koika_types, right associativity).

(* Koika_branches *)
Notation "x '=>' a " := (cons (x,a) nil) (in custom koika_branches at level 60, x custom koika at level 99, a custom koika at level 89).
Notation "arg1 '|' arg2" := (app arg1 arg2) (in custom koika_branches at level 13, arg1 custom koika_branches, arg2 custom koika_branches, format "'[v' arg1 ']' '/' '|'  '[v' arg2 ']'").

(* Koika *)
Notation "'{{' e '}}'" := (e) (e custom koika at level 200, format "'{{' '[v' '/' e '/' ']' '}}'").
Notation "'fail'" :=
  (UFail (bits_t 0)) (in custom koika, format "'fail'").
Notation "'fail' '(' t ')'" :=
  (UFail (bits_t t)) (in custom koika, t constr at level 0 ,format "'fail' '(' t ')'").
Notation "'fail' '@(' t ')'" :=
  (UFail t) (in custom koika, t constr at level 0 ,format "'fail' '@(' t ')'").
Notation "'pass'" := (USugar (UConstBits Ob)) (in custom koika).
Notation "'magic'" := (USugar UErrorInAst) (in custom koika).

Notation "'let' a ':=' b 'in' c" := (UBind a b c) (in custom koika at level 91, a custom koika_var at level 1, right associativity, format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").
Notation "a ';' b" := (USeq a b) (in custom koika at level 90, format "'[v' a ';' '/' b ']'" ).
Notation "'set' a ':=' b" := (UAssign a b) (in custom koika at level 89, a custom koika_var at level 1, format "'set'  a  ':='  b").
Notation "'(' a ')'" := (a) (in custom koika at level 1, a custom koika, format "'[v' '(' a ')' ']'").

Notation "instance  '.(' method ')' args" :=
  (USugar (UCallModule instance id method args))
    (in custom koika at level 1, instance constr at level 0, method constr, args custom koika_args at level 99).
Notation "'{' method '}' args" :=
  (UInternalCall method args)
    (in custom koika at level 1, method constr at level 200 , args custom koika_args at level 99, only parsing).
Notation "method args" :=
  (UInternalCall method args)
    (in custom koika at level 1, method constr at level 0 , args custom koika_args at level 99, only parsing).

Notation "a" := (UVar (ident_to_string a)) (in custom koika at level 1, a constr at level 0, only parsing).
Notation "a" := (UVar a) (in custom koika at level 1, a constr at level 0, only printing).

Notation "'read0' '(' reg ')' " := (URead P0 reg) (in custom koika, reg constr, format "'read0' '(' reg ')'").
Notation "'read1' '(' reg ')' " := (URead P1 reg) (in custom koika, reg constr, format "'read1' '(' reg ')'").
Notation "'write0' '(' reg ',' value ')'" :=
  (UWrite P0 reg value)
    (in custom koika, reg constr at level 13, format "'write0' '(' reg ',' value ')'").
Notation "'write1' '(' reg ',' value ')'" :=
  (UWrite P1 reg value)
    (in custom koika, reg constr at level 13, format "'write1' '(' reg ',' value ')'").

Notation "'if' a 'then' t 'else' f" := (UIf a t f) (in custom koika at level 30, right associativity, format "'[v' 'if'  a '/' 'then'  t '/' 'else'  f ']'").
Notation "'guard' '(' a ')' " := (UIf a (USugar (UConstBits Ob)) (UFail (bits_t 0))) (in custom koika at level 30, right associativity, format "'guard' '(' a ')'").
Notation "'when' a 'do' t " := (UIf a t (USugar (UConstBits Ob))) (in custom koika at level 91, right associativity, format "'[v' 'when'  a '/' 'do'  t '/' ']'").

Notation "a '&&' b" :=  (UBinop (UBits2 UAnd) a b) (in custom koika at level 80,  right associativity, format "a  '&&'  b").
Notation "'!' a" := (UUnop (UBits1 UNot) a) (in custom koika at level 75, a custom koika at level 99, format "'!' a").
Notation "a '||' b" :=  (UBinop (UBits2 UOr) a b) (in custom koika at level 85, format "a  '||'  b").
Notation "'zeroExtend(' a ',' b ')'" :=  (UUnop (UBits1 (UZExtL b)) a) (in custom koika, b constr at level 0, format "'zeroExtend(' a ',' b ')'").
Notation "a '^' b" :=  (UBinop (UBits2 UXor) a b) (in custom koika at level 85, format "a  '^'  b").
Notation "a '+' b" :=  (UBinop (UBits2 UPlus) a b) (in custom koika at level 85, format "a  '+'  b").
Notation "a '-' b" :=  (UBinop (UBits2 UMinus) a b) (in custom koika at level 85, format "a  '-'  b").
Notation "a '==' b" :=  (UBinop UEq a b) (in custom koika at level 79, format "a  '=='  b").
Notation "a '>>' b" :=  (UBinop (UBits2 ULsr) a b) (in custom koika at level 79, format "a  '>>'  b").
Notation "a '<<' b" :=  (UBinop (UBits2 ULsl) a b) (in custom koika at level 79, format "a  '<<'  b").
Notation "a  '<'  b" := (UBinop (UBits2 (UCompare false cLt)) a b) (in custom koika at level 79).
Notation "a  '<s'  b" := (UBinop (UBits2 (UCompare true cLt)) a b) (in custom koika at level 79).
Notation "a  '<='  b" := (UBinop (UBits2 (UCompare false cLe)) a b) (in custom koika at level 79).
Notation "a  '<s='  b" := (UBinop (UBits2 (UCompare true cLe)) a b) (in custom koika at level 79).
Notation "a  '>'  b" := (UBinop (UBits2 (UCompare false cGt)) a b) (in custom koika at level 79).
Notation "a  '>s'  b" := (UBinop (UBits2 (UCompare true cGt)) a b) (in custom koika at level 79).
Notation "a  '>='  b" := (UBinop (UBits2 (UCompare false cGe)) a b) (in custom koika at level 79).
Notation "a  '>s='  b" := (UBinop (UBits2 (UCompare true cGe)) a b) (in custom koika at level 79).
Notation "a '++' b" :=  (UBinop (UBits2 UConcat) a b) (in custom koika at level 80,  right associativity, format "a  '++'  b").
Notation "a '[' b ']'" := (UBinop (UBits2 USel) a b) (in custom koika at level 75, format "'[' a [ b ] ']'").
(* Notation "a '[' b ':' c ']'" := (UBinop (UBits2 (UIndexedPart c)) a b) (in custom koika at level 75, c constr at level 0, format "'[' a [ b ':+' c ] ']'"). *)
Notation "a '[' b ':+' c ']'" := (UBinop (UBits2 (UIndexedPart c)) a b) (in custom koika at level 75, c constr at level 0, format "'[' a [ b ':+' c ] ']'").
Notation "'`' a '`'" := ( a) (in custom koika at level 99, a constr at level 99).

Notation "'fun' args ':' ret '=>' body" :=
  {| int_name := "";
     int_argspec := args;
     int_retType := ret;
     int_body := body |}
    (in custom koika at level 99, args custom koika_types, ret constr at level 0, body custom koika at level 99, format "'[v' 'fun'  args  ':'  ret  '=>' '/' body ']'").
Notation "'fun' '_' ':' ret '=>' body" :=
  {| int_name := "";
     int_argspec := nil;
     int_retType := ret;
     int_body := body |}
    (in custom koika at level 99,  ret constr at level 0, body custom koika at level 99, format "'[v' 'fun'  '_'   ':'  ret  '=>' '/' body ']'").

(* Deprecated *)
Notation "'call' instance method args" :=
  (USugar (UCallModule instance id method args))
    (in custom koika at level 99, instance constr at level 0, method constr at level 0, args custom koika_args).
Notation "'funcall' method args" :=
  (UInternalCall method args)
    (in custom koika at level 98, method constr at level 0, args custom koika_args).
Notation "'call0' instance method " :=
  (UCallModule instance id method nil)
    (in custom koika at level 98, instance constr at level 0, method constr).
Notation "'funcall0' method " :=
  (UInternalCall method nil)
    (in custom koika at level 98,  method constr at level 0).

Notation "'get' '(' t ',' f ')'" :=
  (UUnop (UStruct1 (UGetField f)) t)
    (in custom koika, t custom koika at level 13, f custom koika_var at level 0, format "'get' '(' t ','  f ')'").
Notation "'subst' '(' t ',' f ',' a ')'" :=
  (UBinop (UStruct2 (USubstField f)) t a)
    (in custom koika, t custom koika at level 13, a custom koika at level 13, f custom koika_var at level 0, format "'subst' '(' t ','  f ',' a ')'").

Declare Custom Entry koika_structs_init.

Notation "f ':=' expr" := (cons (f,expr) nil) (in custom koika_structs_init at level 20, f custom koika_var at level 0, expr custom koika at level 88).
Notation "a ';' b" := (app a b) (in custom koika_structs_init at level 99, a custom koika_structs_init).
Notation "'struct' structtype '{|' fields '|}'" :=
  (USugar (UStructInit structtype fields)) (in custom koika, structtype constr at level 0, fields custom koika_structs_init at level 92).

Notation "'enum' enum_type '{|' f '|}'" :=
  (USugar (UConstEnum enum_type f))
    (in custom koika at level 1, enum_type constr at level 1, f custom koika_var at level 1).

Notation "'match' var 'with' '|' branches 'return' 'default' ':' default 'end'" :=
  (UBind "__reserved__matchPattern" var (USugar (USwitch (UVar "__reserved__matchPattern") default branches)))
    (in custom koika at level 30,
        var custom koika,
        branches custom koika_branches,
        default custom koika ,
        format "'match'  var  'with' '/' '[v'  '|'  branches '/' 'return'  'default' ':' default ']' 'end'").

Notation "'#' s" := (USugar (UConstBits s)) (in custom koika at level 98, s constr at level 0 ).


Notation "r '|>' s" :=
  (UCons r s)
    (at level 99, s at level 99, right associativity).
Notation "'done'" :=
  UDone (at level 99).

Module Type Tests.
  Parameter pos_t : Type.
  Parameter fn_name_t : Type.
  Parameter reg_t : Type.
  Parameter ext_fn_t : Type.
  Notation uaction reg_t := (uaction pos_t string fn_name_t reg_t ext_fn_t).
  Definition test_2 : uaction reg_t := {{ yo; yoyo }}.
  Definition test_3 : uaction reg_t := {{ set  yoyo := `UVar "magic" : uaction reg_t`  }}.
  Definition test_1 : uaction reg_t := {{ let yoyo := fail(2) in magic }}.
  Definition test_1' : uaction reg_t := {{ let yoyo := fail(2) in yoyo }}.
  Definition test_2' : uaction reg_t := {{ magic; magic }}.
  Definition test_3' : uaction reg_t := {{ set yoyo := magic ; magic }}.
  Definition test_4 : uaction reg_t := {{ magic ; set yoyo := magic }}.
  Definition test_5 : uaction reg_t := {{ let yoyo := set yoyo := magic in magic }}.
  Definition test_6 : uaction reg_t := {{ let yoyo := set yoyo := magic; magic in magic;magic }}.
  Definition test_7 : uaction reg_t := {{ (let yoyo := (set yoyo := magic); magic in magic;magic) }}.
  Definition test_8 : uaction reg_t := {{ (let yoyo := set yoyo := magic; magic in magic);magic }}.
  Inductive test : Set := |rData (n:nat).
  Axiom data0 : reg_t.
  Axiom data1 : reg_t.
  Definition test_9 : uaction reg_t := {{ read0(data0) }}.
  Definition test_10 : nat -> uaction test := (fun idx => {{ read0(rData idx) }}).
  Definition test_11 : uaction reg_t := {{ (let yoyo := read0(data0) in write0(data0, magic)); fail }}.
  Definition test_12 : uaction reg_t := {{ (let yoyo := if fail then read0(data0) else fail in write0(data0,magic));fail }}.
  Definition test_13 : uaction reg_t := {{ yoyo }}.
  Definition test_14 : uaction reg_t := {{ !yoyo && yoyo }}.
  Definition test_14' : uaction reg_t := {{ !(yoyo && yoyo) }}.
  Definition test_15 : uaction reg_t := {{ yoyo && read0(data0) }}.
  Definition test_16 : uaction reg_t := {{ !read0(data1) && !read0(data1) }}.
  Definition test_17 : uaction reg_t := {{ !read0(data1) && magic}}.
  Definition test_18 : uaction reg_t := {{ !read0(data1) && Yoyo }}.
  Definition test_19 : uaction reg_t := {{ yoy [ oio && ab ] && Ob~1~0 }}.
  Definition test_20 : uaction reg_t := {{ yoyo [ magic :+ 3 ] && yoyo }}.
  Definition test_20' : uaction reg_t := {{ (yoyo [ magic :+ 3]  ++ yoyo) && yoyo }}.
  Definition test_20'' : uaction reg_t := {{ ( yoyo [ magic :+ 3 ] ++ yoyo ++bla) && yoyo }}.

  (* Notation "'{&' a '&}'" := (a) (a custom koika_types at level 200). *)
  (* Definition test_21 := {& "yoyo" : bits_t 2 &}. *)
  (* Definition test_22 := {& "yoyo" : bits_t 2 , "yoyo" : bits_t 2  &}. *)
  Definition test_23 : InternalFunction string string (uaction reg_t) := {{ fun (arg1 : (bits_t 3)) (arg2 : bits_t 2) : bits_t 4 => magic }}.
  Definition test_24 : nat -> InternalFunction string string (uaction reg_t) :=  (fun sz => {{ fun  (arg1 : bits_t sz) (arg1 : bits_t sz) : bits_t sz  => magic}}).
  Definition test_25 : nat -> InternalFunction string string (uaction reg_t) := (fun sz => {{fun (arg1 : bits_t sz ) : bits_t sz => let oo := magic >> magic in magic}}).
  Definition test_26 : nat -> InternalFunction string string (uaction reg_t) := (fun sz => {{ fun _ : bits_t sz  => magic }}).
  Definition test_27 : uaction reg_t :=
    {{
        (if (!read0(data0)) then
           write0(data0, Ob~1);
             let yo := if (dlk == Ob~1 ) then bla else yoyo || foo
             in
             write0(data0, Ob~1)
         else
           read0(data0));
        fail
    }}.
  Definition test_28 : uaction reg_t :=  {{
                                             match var with
                                             | magic => magic
                                             return default: magic
                                             end
                                         }}.

  Definition mem_req :=
    {| struct_name := "mem_req";
       struct_fields := cons ("type", bits_t 1)
                             nil |}.

  Definition test_30'' : uaction reg_t :=
    {{
        struct mem_req {| foo := upu[#(Bits.of_nat 3 0) :+ 2] ; bar := |32`d98| |}
    }}.

  Definition test_29 : uaction reg_t :=
    {{
        struct mem_req {| foo := upu; bar := magic |}
    }}.

End Tests.