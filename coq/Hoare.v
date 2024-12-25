(* Implementing hoare logic for koika's evaluation *)
Require Import Unicode.Utf8.

Require Import Koika.TypedSyntax.
Require Import Koika.TypedSemantics.

Section Hoare.

  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Notation action := (action pos_t var_t fn_name_t R Sigma).

  (* Register environment a Map-Type from register names to their values *)
  Context {REnv: Env reg_t}.

  Context {sig: tsig var_t}.

  Definition assertion := tcontext sig -> Log R REnv -> REnv.(env_t) R -> Prop.

  Inductive HoareTriple {tau: type} : assertion -> action sig tau -> assertion -> Prop :=
  | HTSeq : ∀ P Q R a1 a2,
    HoareTriple P a1 Q -> HoareTriple Q a2 R ->
    HoareTriple P (Seq a1 a2) R.

  Declare Scope log_scope.
  Notation "[]" := log_empty : log_scope.
  Bind Scope log_scope with Log.

  Definition interp_action_update_env {tau} env sigma Gamma slog alog (act : action sig tau) :=
    option_map (fun '(l, r, Gamma') => (commit_update env l, r, Gamma')) (interp_action (REnv := REnv) env sigma Gamma slog alog act).

  Theorem hoare_triple_interp_action {tau} : ∀ P (a : action sig tau) Q,
    HoareTriple P a Q ->
    ∀ env log Γ Γ' sigma r slog alog,
    P Γ alog env ->
    interp_action env sigma Γ slog alog a = Some (log, r, Γ') ->
    Q Γ' log env.
  Proof.
    induction 1.
    - intros.
      simpl in H2.
      destruct (interp_action env sigma Γ slog alog a1) eqn:Heq; inversion H2.
      do 2 destruct p. clear H2.
      specialize (IHHoareTriple1 _ _ _ _ _ _ _ _ H1 Heq).
      specialize (IHHoareTriple2 _ _ _ _ _ _ _ _ IHHoareTriple1 H4).
      assumption.
  Qed.
