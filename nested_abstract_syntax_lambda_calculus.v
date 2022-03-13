(** The goal of this text is to present the "nested abstract syntax".
It is a technique for representing bound variables in formal languages, using the coq 
option operator (which adds exactly one new object to a given set or type).
Implementing bound variables may be an issue because of the variable capture phenomenon and 
the need to describe precisely and implement alpha renaming in order to avoid it.
The following method avoids these problematics entirely.
Other better known techniques which achieve this are De Bruijn indices and the locally 
nameless convention.

Here, the idea consists roughly, from a given context C (i.e. a set of 
constants/names/variables or call these whatever you like), to add a new bound variable to 
that context with the option operator, so that if f is a term on the context (option C), then 
"lambda f" is a term in the context X. (it would be "lambda x f" if the new object was 
"x" in the more usual notation but we don't need to indicate which new variable is, it is 
just the new object introduced by "option" ). 

The nested abstract syntax was introduced in that paper from André Hirschowitz and 
Marco Maggesi:
https://math.unice.fr/~ah/div/fsubwf.pdf

The language we use below in order to show how nested abstract syntax works is untyped 
lambda calculus.  
The idea is (in the opinion of the author) very easy to grasp and once you've understood it,
you can immediately use it for any other kind of formalized language, e.g. it is possible
to develop first order logic and its proof theory, and prove meta theorems without ever having
to deal with the tedious issues of alpha renaming. 

*)

(** Pros: 
-No alpha renaming, like with De Bruijn indices based methods.
-This approach is extremely simple conceptually.

Cons: 
-if you want to use this idea to implement for instance 
lambda calculus in other programming languages, the type system 
has to be flexible enough; for instance when the following is ported in OCaml by the 
COQ extraction mechanism,O bj.magic will be used (resp. unsafe coerces in Haskell). But is 
it actually an issue?
-Performance (?): actually I've tested it only on very small examples so I don't know what 
happens with large data.
*)

Section Definition_of_main_objects_and_operations.

  Inductive Lambda_Term (context:Set):Set:=
  |lt_var: context -> Lambda_Term context
  |lt_app: Lambda_Term context -> Lambda_Term context -> Lambda_Term context
  |lt_abs: Lambda_Term (option context) -> Lambda_Term context.

  (** We recall what the Coq operator "option_map" is:

  option_map = 
  fun (A B : Type) (f : A -> B) (o : option A) =>
  match o with
  | Some a => Some (f a)
  | None => None
  end
  : forall A B : Type, (A -> B) -> option A -> option B

  Arguments A, B are implicit
  Argument scopes are [type_scope type_scope function_scope _]
   *)

  Fixpoint lt_change_of_variables (C:Set) (f:Lambda_Term C) (D:Set) (var_env: C -> D)
           {struct f}: Lambda_Term D:=
    match f with
    |lt_var _ l => lt_var D (var_env l)
    |lt_app _ x y => lt_app
                       D
                       (lt_change_of_variables C x D var_env)
                       (lt_change_of_variables C y D var_env)
    |lt_abs _ g => lt_abs
                     D
                     (lt_change_of_variables (option C) g (option D) (option_map var_env))
    end.

  Definition lt_constant_embedding (C:Set) (f:Lambda_Term C): Lambda_Term (option C):=
    lt_change_of_variables C f (option C) Some.

  Definition lt_extend_environment (C D:Set) (env: C -> Lambda_Term D) (o:option C):
    Lambda_Term (option D):=
    match o with
    | Some l => lt_constant_embedding D (env l)
    | None => lt_var (option D) None
    end.

  Fixpoint lt_substitution (C:Set) (f:Lambda_Term C) (D:Set) (env: C -> Lambda_Term D)
           {struct f}: Lambda_Term D:=
    match f with
    |lt_var _ l => env l
    |lt_app _ x y => lt_app
                       D
                       (lt_substitution C x D env)
                       (lt_substitution C y D env)
    |lt_abs _ g => lt_abs
                     D
                     (lt_substitution (option C) g (option D) (lt_extend_environment C D env))
    end.

  Definition lt_set_new_variable (C:Set) (t:Lambda_Term C) (o:option C):Lambda_Term C:=
    match o with
    |Some l => lt_var C l
    |None => t
    end.

  Definition lt_specify_new_var (C:Set) (f:Lambda_Term (option C)) (t:Lambda_Term C):=
    lt_substitution (option C) f C (lt_set_new_variable C t).  

  Section abstraction_and_specification_with_respect_to_other_variables.

    Variable C:Set.
    Variable equality_test_context: forall x y:C, sumbool (x=y) (x<>y).

  Definition lt_set_variable (x:C) (t:Lambda_Term C) (y:C):Lambda_Term C:=
    match (equality_test_context x y) with
    |left _ => t
    |right _ => lt_var C y
    end.

  Definition lt_specify (f:Lambda_Term C) (x:C) (t:Lambda_Term C):Lambda_Term C:=
    lt_substitution C f C (lt_set_variable x t). 
  
  Definition lt_set_variable_to_new_variable (x y:C):option C:=
    match (equality_test_context x y) with
    |left _ => None
    |right _ => Some y
    end.

  Definition lt_lambda (x:C) (f:Lambda_Term C):Lambda_Term C:=
    lt_abs C (lt_change_of_variables C f (option C) (lt_set_variable_to_new_variable x)).  
    
  End abstraction_and_specification_with_respect_to_other_variables.
  
  Section basic_combinators.

    (** We don't use the lt_lambda function we've defined above because the following
     objects are relevant for any C, even if there isn't any equality test on it. *)
    
    Notation "^ A":= (option A) (right associativity, at level 31).

    Definition lt_k (C:Set):Lambda_Term C:=
      lt_abs C (lt_abs (^C) (lt_var (^^C)(Some None))).

    Definition lt_s (C:Set):Lambda_Term C:=
      lt_abs
        C
        (lt_abs
           (^C)
           (lt_abs
              (^^C)
              (lt_app (^^^C)
                      (lt_app (^^^C)
                              (lt_var (^^^C) (Some (Some None)))
                              (lt_var (^^^C) None)
                      )
                      (lt_app (^^^C)
                              (lt_var (^^^C) (Some None))
                              (lt_var (^^^C) None)
                      )
              )
           )
        ).
    
  End basic_combinators.
  
End Definition_of_main_objects_and_operations.

Section equalities_involving_change_of_variables_and_substitution.
  
  Fixpoint lt_cov_pointwise_equality
           (C:Set) (f:Lambda_Term C)(D:Set)
           (var_env1 var_env2: C -> D)
           (eqenv: forall i:C, var_env1 i = var_env2 i)
           {struct f}:
    lt_change_of_variables C f D var_env1 =
    lt_change_of_variables C f D var_env2.
  Proof.
    destruct f.
    simpl; apply f_equal; apply eqenv.
    simpl. repeat rewrite lt_cov_pointwise_equality
             with (D:=D) (var_env1:= var_env1) (var_env2:= var_env2). reflexivity.
    assumption. assumption.
    simpl. apply f_equal. apply lt_cov_pointwise_equality.
    intros; destruct i. simpl; rewrite eqenv; reflexivity. simpl; reflexivity.
  Defined.

  Fixpoint lt_cov_composition_equality
           (C:Set) (f:Lambda_Term C) (D E:Set)
           (env_cd: C -> D) 
           (env_de: D -> E)
           {struct f}:
    lt_change_of_variables D (lt_change_of_variables C f D env_cd) E env_de =
    lt_change_of_variables C f E
                           (fun i:C => env_de (env_cd i)).
  Proof.
    destruct f.
    simpl; reflexivity.
    simpl; apply f_equal2.
    apply lt_cov_composition_equality. apply lt_cov_composition_equality. 
    simpl; apply f_equal.
    rewrite lt_cov_composition_equality. apply lt_cov_pointwise_equality.
    intros; destruct i. simpl; reflexivity. simpl; reflexivity.
  Defined.  

  Fixpoint lt_cov_identity_equality
           (C:Set) (f:Lambda_Term C) {struct f}:
    lt_change_of_variables C f C (fun v:C => v) = f.
  Proof.
    destruct f. simpl; reflexivity. simpl; apply f_equal2. apply lt_cov_identity_equality.
    apply lt_cov_identity_equality. simpl. apply f_equal.
    rewrite lt_cov_pointwise_equality with (var_env2:= fun o:option C => o).
    apply lt_cov_identity_equality. intros. destruct i.
    simpl; reflexivity. simpl; reflexivity.
  Defined.
  
  Fixpoint lt_sub_pointwise_equality
           (C:Set) (f:Lambda_Term C)(D:Set)
           (env1 env2: C -> Lambda_Term D)
           (eqenv: forall i:C, env1 i = env2 i)
           {struct f}:
    lt_substitution C f D env1 =
    lt_substitution C f D env2.
  Proof.
    destruct f.
    simpl; apply eqenv.
    simpl; apply f_equal2. apply lt_sub_pointwise_equality; assumption.
    apply lt_sub_pointwise_equality; assumption.
    simpl. apply f_equal. apply lt_sub_pointwise_equality.
    intro. destruct i.
    simpl. apply f_equal; apply eqenv. reflexivity.
  Defined.

  Fixpoint lt_sub_after_cov_equality 
           (C:Set) (f:Lambda_Term C) (D E:Set)
           (env_cd: C -> D) 
           (env_de: D -> Lambda_Term E)
           {struct f}:
    lt_substitution D (lt_change_of_variables C f D env_cd) E env_de =
    lt_substitution C f E (fun i:C => env_de (env_cd i)).
  Proof.
    destruct f.
    simpl; reflexivity.
    simpl; apply f_equal2.
    apply lt_sub_after_cov_equality. apply lt_sub_after_cov_equality. 
    simpl; apply f_equal.
    rewrite lt_sub_after_cov_equality. apply lt_sub_pointwise_equality.
    intros. destruct i. simpl. unfold lt_constant_embedding.
    repeat rewrite lt_cov_composition_equality. apply lt_cov_pointwise_equality.
    intros; simpl; reflexivity.
    simpl; reflexivity.
  Defined.

  Fixpoint lt_cov_after_sub_equality 
           (C:Set) (f:Lambda_Term C) (D E:Set)
           (env_cd: C -> Lambda_Term D) 
           (env_de: D -> E)
           {struct f}:
    lt_change_of_variables D (lt_substitution C f D env_cd) E env_de =
    lt_substitution C f E
                    (fun i:C => lt_change_of_variables D (env_cd i) E env_de).
  Proof.
    destruct f.
    simpl; reflexivity.
    simpl; apply f_equal2.
    apply lt_cov_after_sub_equality. apply lt_cov_after_sub_equality. 
    simpl; apply f_equal.
    rewrite lt_cov_after_sub_equality. apply lt_sub_pointwise_equality.
    intros. destruct i. simpl. unfold lt_constant_embedding.
    repeat rewrite lt_cov_composition_equality.
    apply lt_cov_pointwise_equality.
    intros; simpl; reflexivity.
    simpl; reflexivity.
  Defined.
  
  Fixpoint lt_sub_composition_equality
           (C:Set) (f:Lambda_Term C) (D E:Set)
           (env_cd: C -> Lambda_Term D) 
           (env_de: D -> Lambda_Term E)
           {struct f}:
    lt_substitution D (lt_substitution C f D env_cd) E env_de =
    lt_substitution C f E (fun i:C => lt_substitution D (env_cd i) E env_de).
  Proof.
    destruct f.
    simpl; reflexivity.
    simpl; apply f_equal2. apply lt_sub_composition_equality. apply lt_sub_composition_equality. 
    simpl; apply f_equal.
    rewrite lt_sub_composition_equality. apply lt_sub_pointwise_equality.
    intros. destruct i. simpl. unfold lt_constant_embedding.
    rewrite lt_cov_after_sub_equality.
    rewrite lt_sub_after_cov_equality.
    reflexivity. simpl. reflexivity.
  Defined.

  Fixpoint lt_sub_identity_equality
           (C:Set) (f:Lambda_Term C) 
           {struct f}:
    lt_substitution C f C (lt_var C) = f.
  Proof.
    destruct f.
    simpl; reflexivity.
    simpl; apply f_equal2. apply lt_sub_identity_equality. apply lt_sub_identity_equality.
    simpl; apply f_equal. rewrite lt_sub_pointwise_equality with (env2:= lt_var (option C)).
    apply lt_sub_identity_equality.
    intros; destruct i. simpl; reflexivity. simpl; reflexivity.
  Defined.      
  
  Definition lt_specify_new_var_constant: forall (C:Set) (f t:Lambda_Term C),
      lt_specify_new_var C (lt_constant_embedding C f) t = f.
  Proof.
    intros.
    unfold lt_specify_new_var. unfold lt_constant_embedding.
    rewrite lt_sub_after_cov_equality.
    rewrite lt_sub_pointwise_equality with (env2:= lt_var C).
    apply lt_sub_identity_equality.
    intros; simpl; reflexivity.
  Defined.

  Definition lt_specify_new_var_cov:
    forall (C D:Set) (var_env: C -> D) (f:Lambda_Term (option C))
           (t:Lambda_Term C),
      lt_change_of_variables C (lt_specify_new_var C f t) D var_env = 
      lt_specify_new_var
        D
        (lt_change_of_variables (option C) f (option D)
                                (option_map var_env))
        (lt_change_of_variables C t D var_env).
  Proof.
    intros.
    unfold lt_specify_new_var. rewrite lt_cov_after_sub_equality.
    rewrite lt_sub_after_cov_equality.
    apply lt_sub_pointwise_equality. 
    intros; destruct i. simpl; reflexivity. simpl; reflexivity.
  Defined.

  Definition lt_specify_new_var_sub:
    forall (C D:Set) (env: C -> Lambda_Term D) (f:Lambda_Term (option C))
           (t:Lambda_Term C),
      lt_substitution C (lt_specify_new_var C f t) D env = 
      lt_specify_new_var
        D
        (lt_substitution (option C) f (option D) (lt_extend_environment C D env))
        (lt_substitution C t D env).
  Proof.
    intros.
    unfold lt_specify_new_var.
    repeat rewrite lt_sub_composition_equality.
    apply lt_sub_pointwise_equality. intros; destruct i. simpl. unfold lt_constant_embedding.
    rewrite lt_sub_after_cov_equality.
    rewrite lt_sub_pointwise_equality with (env2 := lt_var D).
    apply eq_sym; apply lt_sub_identity_equality.
    intros; simpl; reflexivity.
    simpl; reflexivity.
  Defined.

  Definition lt_specify_variable:
    forall (C:Set) (f:Lambda_Term (option C)),
      lt_specify_new_var
        (option C)
        (lt_change_of_variables
           (option C)
           f
           (option (option C))
           (option_map Some))                    
        (lt_var (option C) (None)
        ) = f.
  Proof.
    intros.
    unfold lt_specify_new_var.
    rewrite lt_sub_after_cov_equality.
    rewrite lt_sub_pointwise_equality with (env2:= lt_var (option C)).
    apply lt_sub_identity_equality.
    intros; destruct i. simpl; reflexivity. simpl; reflexivity.
  Defined.

End equalities_involving_change_of_variables_and_substitution.

Section readables_terms_and_translations.

  (** In this section, a much more usual definition of lambda terms is introduced.
      We start from a countable set of variables (a context: it will simply be the set
      of positive integers "nat" and define inductively lambda terms exactly in the way
      it is done in textbooks (we call these "Readable Lambda Terms"; in 
      some project this would be what the user deal with while terms defined
      with nested abstract syntax would be more used internally).
      Translations between both syntax are provided and allow use to define a 
      capture-free operation (we pick a readable term, translate it into a nested abstract 
      syntax term on which we perform the substitution and then translate back the term
      obtained.                   
   *)

  Section dec_nat.

    (** first we need boolean equality test for naturals is needed.*)

    Fixpoint eq_dec_nat (p q:nat) {struct p}: sumbool (p = q) (p <> q):=
      match p as n return ({n = q} + {n <> q}) with
      | 0 =>
        match q as n return ({0 = n} + {0 <> n}) with
        | 0 => left eq_refl
        | S q0 =>
          right
            (fun H : 0 = S q0 =>
               let H0 : False :=
                   eq_ind 0 (fun e : nat => match e with
                                            | 0 => True
                                            | S _ => False
                                            end) I (S q0) H in
               False_ind False H0)
        end
      | S p0 =>
        match q as n return ({S p0 = n} + {S p0 <> n}) with
        | 0 =>
          right
            (fun H : S p0 = 0 =>
               let H0 : False :=
                   eq_ind (S p0) (fun e : nat => match e with
                                                 | 0 => False
                                                 | S _ => True
                                                 end) I 0 H in
               False_ind False H0)
        | S q0 =>
          let s := eq_dec_nat p0 q0 in
          match s with
          | left yes => left (eq_S p0 q0 yes)
          | right no => right (fun f : S p0 = S q0 => no (eq_add_S p0 q0 f))
          end
        end
      end.
    
  End dec_nat.

  Inductive Readable_Lambda_Term:Set:=
  |rlt_var: nat -> Readable_Lambda_Term
  |rlt_app: Readable_Lambda_Term -> Readable_Lambda_Term -> Readable_Lambda_Term
  |rlt_lambda: nat -> Readable_Lambda_Term -> Readable_Lambda_Term.

  Fixpoint rlt_to_lt (f:Readable_Lambda_Term) {struct f}:Lambda_Term nat:=
    match f with
    |rlt_var v => lt_var nat v
    |rlt_app a b => lt_app nat (rlt_to_lt a) (rlt_to_lt b)
    |rlt_lambda x g => lt_lambda nat eq_dec_nat x (rlt_to_lt g)
    end.

  Fixpoint lt_to_rlt_aux (C:Set) (t:Lambda_Term C) (aux_env:C -> nat) (index:nat) {struct t}:
    Readable_Lambda_Term:=
    match t with
    |lt_var _ v => rlt_var (aux_env v)
    |lt_app _ p q => rlt_app (lt_to_rlt_aux C p aux_env index)
                             (lt_to_rlt_aux C q aux_env index)
    |lt_abs _ u => rlt_lambda
                     index
                     (lt_to_rlt_aux
                        (option C)
                        u
                        (fun o:option C => match o with
                                           |Some w => aux_env w
                                           |None => index
                                           end)
                        (S index)
                     )
    end.

  Inductive lt_free_variable (C:Set) (x:C): Lambda_Term C -> Prop:=
  |ltfv_atom: lt_free_variable C x (lt_var C x)
  |ltfv_app_left: forall a b:Lambda_Term C,
      lt_free_variable C x a -> lt_free_variable C x (lt_app C a b)
  |ltfv_app_right: forall a b:Lambda_Term C,
      lt_free_variable C x b -> lt_free_variable C x (lt_app C a b)
  |ltfv_abs: forall f:Lambda_Term (option C),
      lt_free_variable (option C) (Some x) f -> lt_free_variable C x (lt_abs C f).

  Fixpoint lt_cov_free_variable_pointwise_equality
           (C:Set) (f:Lambda_Term C)(D:Set)
           (var_env1 var_env2: C -> D)
           (eqenv: forall i:C, lt_free_variable C i f -> var_env1 i = var_env2 i)
           {struct f}:
    lt_change_of_variables C f D var_env1 =
    lt_change_of_variables C f D var_env2.
  Proof.
    destruct f.
    simpl; apply f_equal; apply eqenv; apply ltfv_atom.
    simpl. repeat rewrite lt_cov_free_variable_pointwise_equality
             with (D:=D) (var_env1:= var_env1) (var_env2:= var_env2). reflexivity.
    intros; apply eqenv; apply ltfv_app_right; assumption.
    intros; apply eqenv; apply ltfv_app_left; assumption.
    simpl. apply f_equal. apply lt_cov_free_variable_pointwise_equality.
    intros; destruct i. simpl; rewrite eqenv. reflexivity. apply ltfv_abs; assumption.
    simpl; reflexivity.
  Defined.

  Lemma no_lt_eq: forall p:nat, p < p -> False.
  Proof.
    unfold lt.
    induction p. intros. inversion H.
    intros. apply le_S_n in H. apply IHp; assumption.
  Defined.
    
  Fixpoint lt_rlt_compatibility_aux (C:Set) (t:Lambda_Term C) {struct t}:
    forall (index:nat) (aux_env: C -> nat),
      (forall x:C, lt_free_variable C x t -> aux_env x < index) ->
      rlt_to_lt (lt_to_rlt_aux C t aux_env index) = lt_change_of_variables C t nat aux_env.
  Proof.
    destruct t.
    intros. simpl. reflexivity.
    intros. simpl. repeat rewrite lt_rlt_compatibility_aux. reflexivity.
    intros; apply H; apply ltfv_app_right; assumption.
    intros; apply H; apply ltfv_app_left; assumption.
    intros. simpl. rewrite lt_rlt_compatibility_aux. unfold lt_lambda.
    apply f_equal. rewrite lt_cov_composition_equality.
    apply lt_cov_free_variable_pointwise_equality. intros.
    unfold lt_set_variable_to_new_variable. 
    destruct i. simpl. destruct (eq_dec_nat index (aux_env c)). apply False_rect.
    apply no_lt_eq with (p:= aux_env c). apply ltfv_abs in H0. apply H in H0.
    rewrite e in H0. assumption. simpl; reflexivity.
    destruct (eq_dec_nat index index). simpl; reflexivity. apply False_rect. apply n.
    reflexivity. intros. destruct x. apply ltfv_abs in H0. apply H in H0. apply le_S in H0.
    apply H0. apply le_n.
  Defined.

  Fixpoint nat_lt_max_variable_aux (C:Set) (t:Lambda_Term C) (f: C -> nat):nat:=
    match t with
    |lt_var _ v => f v 
    |lt_app _ a b => Nat.max (nat_lt_max_variable_aux C a f) (nat_lt_max_variable_aux C b f)
    |lt_abs _ u => nat_lt_max_variable_aux
                     (option C) u
                     (fun o:option C => match o with
                                        |Some p => f p
                                        |None => 0
                                        end)
    end.

  Fixpoint max_ineq_left (p q:nat) (i:p <= q) (r:nat) {struct q}:
    p <= Nat.max q r.
  Proof.
    destruct q. inversion i. apply le_0_n.  
    simpl. destruct r. assumption. inversion i. apply le_n_S. apply max_ineq_left. apply le_n.
    apply le_S. apply max_ineq_left. assumption.
  Defined.

  Fixpoint max_ineq_right (p q:nat) (i:p <= q) (r:nat) {struct q}:
    p <= Nat.max r q.
  Proof.
    destruct q. inversion i. apply le_0_n.  
    destruct r. simpl. assumption. simpl. inversion i. apply le_n_S. apply max_ineq_right.
    apply le_n. apply le_S. apply max_ineq_right. assumption.
  Defined.
    
  Fixpoint nat_lt_free_max_variable_inequality
           (C:Set) (x:C) (t:Lambda_Term C) (fv: lt_free_variable C x t) {struct fv}:
    forall (f:C -> nat),
      f x <=  nat_lt_max_variable_aux C t f.
  Proof.
    destruct fv.
    intros; simpl. apply le_n.
    intros; simpl; apply max_ineq_left; apply nat_lt_free_max_variable_inequality; assumption.
    intros; simpl; apply max_ineq_right; apply nat_lt_free_max_variable_inequality; assumption.
    intros; simpl.
    apply nat_lt_free_max_variable_inequality with
        (x:= Some x)
        (f:= fun o:option C => match o with | Some p => f0 p | None => 0 end).
    assumption.
  Defined.
  
  Definition lt_to_rlt (t:Lambda_Term nat): Readable_Lambda_Term:=
    lt_to_rlt_aux
      nat
      t
      (fun k:nat => k)
      (S (nat_lt_max_variable_aux nat t (fun k:nat => k))).

  (** The rlt_to_lt map is surjective and lt_to_rlt is an inverse of it *)
  
  Theorem lt_rlt_compatibility:
    forall u:Lambda_Term nat, rlt_to_lt (lt_to_rlt u) = u.
  Proof.
    intros.
    unfold lt_to_rlt.
    apply eq_trans with (y:= lt_change_of_variables nat u nat (fun k:nat => k)).
    apply lt_rlt_compatibility_aux.
    intros. apply le_n_S.
    apply nat_lt_free_max_variable_inequality with (f:= fun k:nat => k) in H. assumption.
    apply lt_cov_identity_equality.
  Defined.

  (** As an application of the above, we define the capture-free substitution of a variable
   in a (readable) lambda term: the term constructed below is written "f[v:=t]" 
   in the litterature. *)
  
  Definition capture_free_specify
             (f:Readable_Lambda_Term) (v:nat) (t:Readable_Lambda_Term):Readable_Lambda_Term:=
    lt_to_rlt (lt_specify
                 nat
                 eq_dec_nat
                 (rlt_to_lt f)
                 v
                 (rlt_to_lt t)
              ).
  
End readables_terms_and_translations.

Section reductions.

  Section reduction_without_extensionality.

    Variable C:Set.
    
    Inductive lt_weak_reduction: Lambda_Term C -> Lambda_Term C -> Set:=
    |ltwr_redex: forall (f:Lambda_Term (option C)) (t:Lambda_Term C),
        lt_weak_reduction (lt_app C (lt_abs C f) t) (lt_specify_new_var C f t)
    |ltwr_app: forall x x' y y':Lambda_Term C,
        lt_weak_reduction x x' -> lt_weak_reduction y y' ->
        lt_weak_reduction (lt_app C x y) (lt_app C x' y')
    |ltwr_reflexivity: forall x:Lambda_Term C, lt_weak_reduction x x
    |ltwr_transitivity: forall x y z:Lambda_Term C,
        lt_weak_reduction x y -> lt_weak_reduction y z -> lt_weak_reduction x z.

  End reduction_without_extensionality.
  
  Section beta_eta_reduction.

    (** The most common definition of reduction in lambda calculus is the one below;
     the one we defined earlier is weaker but more appropriate for the applications 
     we'll consider later in the text. *)
    
    Inductive lt_beta_eta_reduction (C:Set): Lambda_Term C -> Lambda_Term C -> Set:=
    |ltber_redex: forall (f:Lambda_Term (option C)) (t:Lambda_Term C),
        lt_beta_eta_reduction C (lt_app C (lt_abs C f) t) (lt_specify_new_var C f t)
    |ltber_eta: forall (f: Lambda_Term C),
        lt_beta_eta_reduction
          C 
          (lt_abs C (lt_app (option C) (lt_constant_embedding C f) (lt_var (option C) None)))
          f
    |ltber_app: forall x x' y y':Lambda_Term C,
        lt_beta_eta_reduction C x x' -> lt_beta_eta_reduction C y y' ->
        lt_beta_eta_reduction C (lt_app C x y) (lt_app C x' y')
    |ltber_extensionality: forall (f g:Lambda_Term (option C)),
        lt_beta_eta_reduction (option C) f g ->
        lt_beta_eta_reduction C (lt_abs C f) (lt_abs C g)
    |ltber_reflexivity: forall x:Lambda_Term C, lt_beta_eta_reduction C x x
    |ltber_transitivity: forall x y z:Lambda_Term C,
        lt_beta_eta_reduction C x y -> lt_beta_eta_reduction C y z ->
        lt_beta_eta_reduction C x z.

    Fixpoint weak_to_beta_eta_reduction (C:Set) (a b:Lambda_Term C)
             (w: lt_weak_reduction C a b) {struct w}:
      lt_beta_eta_reduction C a b.
    Proof.
      destruct w.
      apply ltber_redex. apply ltber_app.
      apply weak_to_beta_eta_reduction; assumption.
      apply weak_to_beta_eta_reduction; assumption. apply ltber_reflexivity.
      apply ltber_transitivity with (y:=y).
      apply weak_to_beta_eta_reduction; assumption.
      apply weak_to_beta_eta_reduction; assumption.
    Defined.
    
  End beta_eta_reduction.
    
  Section weak_reductions_and_substitutions.

    Fixpoint ltwr_substitution (C D:Set) (env: C -> Lambda_Term D)
             (x y:Lambda_Term C) (r: lt_weak_reduction C x y) {struct r}:
      lt_weak_reduction D (lt_substitution C x D env) (lt_substitution C y D env).
    Proof.
      destruct r.
      simpl. rewrite lt_specify_new_var_sub. apply ltwr_redex.
      simpl; apply ltwr_app. apply ltwr_substitution; assumption.
      apply ltwr_substitution; assumption. apply ltwr_reflexivity.
      apply ltwr_transitivity with (y:= lt_substitution C y D env).
      apply ltwr_substitution; assumption. apply ltwr_substitution; assumption.
    Defined.
      
  End weak_reductions_and_substitutions.
  
End reductions.

Section list_manipulation.

  Fixpoint lt_list_product
           (C:Set) (f:Lambda_Term C) (l:list (Lambda_Term C)) {struct l}:
    Lambda_Term C:=
    match l with
    | nil => f
    | cons h t => lt_app C (lt_list_product C f t) h
    end.

  Fixpoint iterated_option (n:nat) (A:Set) {struct n}:Set:=
    match n with
    |0 => A
    |S m => option (iterated_option m A)
    end.
  
  Fixpoint lt_multiple_abstraction
           (C:Set) (n:nat) (f:Lambda_Term (iterated_option n C)) {struct n}:Lambda_Term C.
  Proof.
    destruct n. simpl in f. apply f. simpl in f. apply lt_abs in f.
    apply lt_multiple_abstraction in f. assumption.
  Defined.

  Fixpoint list_length (A:Type) (l:list A) {struct l}:nat:=
    match l with
    |nil => 0
    |cons h t => S (list_length A t)
    end.

  Fixpoint lt_list_to_environment (C:Set) (l:list (Lambda_Term C)) {struct l}:
    iterated_option ((list_length (Lambda_Term C) l)) C -> Lambda_Term C.
  Proof.
    destruct l.
    simpl. apply lt_var.
    simpl. intro s.
    destruct s. apply (lt_list_to_environment C l0). apply i. apply l.
  Defined.

  Fixpoint lt_successive_constant_embedding (C:Set) (n:nat) (f:Lambda_Term C) {struct n}:
    Lambda_Term (iterated_option n C):=
    match n with
    |0 => f
    |S k => lt_constant_embedding (iterated_option k C)
                                  (lt_successive_constant_embedding C k f)
    end.

  Fixpoint lt_successive_specify
           (C:Set) (l:list (Lambda_Term C))
           (f:Lambda_Term (iterated_option (list_length (Lambda_Term C) l) C)) {struct l}:
    Lambda_Term C.
  Proof.
    destruct l.
    apply f.
    apply (lt_successive_specify
             C l0
             (lt_specify_new_var
                (iterated_option (list_length (Lambda_Term C) l0) C) f
                (lt_successive_constant_embedding
                   C
                   (list_length (Lambda_Term C) l0)
                   l))).
  Defined.

  Fixpoint ltwr_successive_specify
           (C:Set) (l:list (Lambda_Term C))
           (x y:Lambda_Term (iterated_option (list_length (Lambda_Term C) l) C)) {struct l}:
    lt_weak_reduction (iterated_option (list_length (Lambda_Term C) l) C) x y ->
    lt_weak_reduction C (lt_successive_specify C l x) (lt_successive_specify C l y).
  Proof.
    destruct l. simpl; intro; assumption.
    simpl. intro. apply ltwr_successive_specify.
    apply ltwr_substitution. assumption.
  Defined.
  
  Fixpoint lt_successive_specify_constant (C:Set) (l:list (Lambda_Term C))
           (k:Lambda_Term C) {struct l}:
    lt_successive_specify
      C l
      (lt_successive_constant_embedding C (list_length (Lambda_Term C) l) k) = k.
  Proof.
    destruct l.
    simpl; reflexivity.
    simpl. rewrite lt_specify_new_var_constant.
    apply lt_successive_specify_constant.
  Defined.

  Fixpoint lt_successive_specify_app (C:Set) (l:list (Lambda_Term C))
           (a b:Lambda_Term (iterated_option (list_length (Lambda_Term C) l) C)) {struct l}:
    lt_successive_specify
      C l (lt_app (iterated_option (list_length (Lambda_Term C) l) C) a b) =
    lt_app C (lt_successive_specify C l a) (lt_successive_specify C l b).
  Proof.
    destruct l. simpl; reflexivity.
    simpl. apply lt_successive_specify_app.
  Defined.                                                                              
  
  Fixpoint lt_successive_redex (C:Set) (l:list (Lambda_Term C))
           (f:Lambda_Term (iterated_option (list_length (Lambda_Term C) l) C)) {struct l}:
    lt_weak_reduction
      C 
      (lt_list_product C (lt_multiple_abstraction C (list_length (Lambda_Term C) l) f) l) 
      (lt_successive_specify C l f).
  Proof.
    destruct l.
    simpl; apply ltwr_reflexivity. simpl.
    apply ltwr_transitivity with
        (y:= lt_app C 
                    (lt_successive_specify
                       C l0 (lt_abs (iterated_option (list_length (Lambda_Term C) l0) C) f ))
                    l).
    apply ltwr_app. apply lt_successive_redex. apply ltwr_reflexivity.
    rewrite <- lt_successive_specify_constant with (k:=l) (l:=l0).
    rewrite <- lt_successive_specify_app. apply ltwr_successive_specify.
    rewrite lt_successive_specify_constant. apply ltwr_redex.
  Defined.

  Definition lt_successive_simultaneous (C:Set) (l:list (Lambda_Term C))
             (f:Lambda_Term (iterated_option (list_length (Lambda_Term C) l) C)):
    lt_successive_specify C l f =
    lt_substitution (iterated_option (list_length (Lambda_Term C) l) C) f C 
                    (lt_list_to_environment C l).
  Proof.
    induction l. simpl. apply eq_sym; apply lt_sub_identity_equality.
    simpl. rewrite IHl. rewrite lt_specify_new_var_sub. unfold lt_specify_new_var.
    rewrite lt_sub_composition_equality. apply lt_sub_pointwise_equality.
    intros. destruct i. simpl. unfold lt_set_new_variable. rewrite <- IHl.
    rewrite lt_successive_specify_constant. apply lt_specify_new_var_constant.
    simpl. rewrite <- IHl. apply lt_successive_specify_constant.
  Defined.
  
  Definition lt_simultaneous_redex (C:Set) (l:list (Lambda_Term C))
             (f:Lambda_Term (iterated_option (list_length (Lambda_Term C) l) C)):
    lt_weak_reduction
      C 
      (lt_list_product C (lt_multiple_abstraction C (list_length (Lambda_Term C) l) f) l) 
      (lt_substitution (iterated_option (list_length (Lambda_Term C) l) C) f C 
                       (lt_list_to_environment C l)).
  Proof.
    rewrite <- lt_successive_simultaneous.
    apply lt_successive_redex.
  Defined.     
  
End list_manipulation.

Section elementary_combinators.

  (** We develop elementary combinatory logic and establish translations between 
   combinatory terms and lambda terms, in order to show that our definitions of 
   lambda terms and reduction are well behaved. *)

  Section reductions_involving_the_s_and_k_terms_of_lambda_calculus.

    (** In this preliminary part we deal with the lt_k and lt_s terms defined earlier.
     The list manipulation section purpose was in fact to establish the following 
     relationships.*)

    Variable C:Set.

    Notation "a ° b":= (lt_app C a b) (left associativity, at level 41).
    Notation "a >w b":= (lt_weak_reduction C a b) (at level 51).
    
    Definition ltwr_k: forall x y:Lambda_Term C,
        ((lt_k C) ° x  ° y) >w x.
    Proof.
      intros; apply lt_simultaneous_redex with (l:= cons y (cons x nil)).
    Defined.
    
    Definition ltwr_s: forall x y z:Lambda_Term C,
        (lt_s C) ° x ° y ° z >w x ° z ° (y ° z).
    Proof.
      intros; apply lt_simultaneous_redex with (l:= cons z (cons y (cons x nil))).
    Defined.
    
  End reductions_involving_the_s_and_k_terms_of_lambda_calculus.    
  
  Section combinators_on_a_general_context.
    
    Variable A:Set.

    Inductive C_Term:Set:=
    |ct_var: A -> C_Term
    |ct_k: C_Term
    |ct_s: C_Term
    |ct_app: C_Term -> C_Term -> C_Term.

    Inductive ct_weak_reduction: C_Term -> C_Term -> Set:=
    |cwr_k: forall x y:C_Term, ct_weak_reduction (ct_app (ct_app ct_k x) y) x
    |cwr_s: forall x y z:C_Term,
        ct_weak_reduction
          (ct_app (ct_app (ct_app ct_s x) y) z)
          (ct_app (ct_app x z)
                  (ct_app y z))
    |cwr_app: forall x x' y y':C_Term,
        ct_weak_reduction x x' -> ct_weak_reduction y y' ->
        ct_weak_reduction (ct_app x y) (ct_app  x' y')
    |cwr_reflexivity: forall x:C_Term, ct_weak_reduction x x
    |cwr_transitivity: forall x y z:C_Term,
        ct_weak_reduction x y -> ct_weak_reduction y z -> ct_weak_reduction x z.

    Definition ct_i:C_Term:= ct_app (ct_app ct_s ct_k) ct_k.
    Definition cwr_i: forall x:C_Term, ct_weak_reduction (ct_app ct_i x) x.
    Proof.
      intros. unfold ct_i.
      apply cwr_transitivity with (y:= ct_app (ct_app ct_k x) (ct_app ct_k x)).
      apply cwr_s. apply cwr_k.
    Defined.
    
  End combinators_on_a_general_context.
  
  Fixpoint ct_to_lt (C:Set) (x:C_Term C){struct x}: (Lambda_Term C):=
    match x with
    |ct_var _ j => lt_var C j
    |ct_k _ => lt_k C 
    |ct_s _ => lt_s C
    |ct_app _ y z => lt_app C (ct_to_lt C y) (ct_to_lt C z)
    end.

  Fixpoint ct_to_lt_reduction (C:Set) (x y:C_Term C)
           (r:ct_weak_reduction C x y) {struct r}:
    lt_weak_reduction C (ct_to_lt C x) (ct_to_lt C y).
  Proof.
    destruct r.
    simpl; apply ltwr_k.
    simpl; apply ltwr_s.
    simpl; apply ltwr_app.
    apply ct_to_lt_reduction; assumption. apply ct_to_lt_reduction; assumption.
    apply ltwr_reflexivity.
    apply ltwr_transitivity with (y:= ct_to_lt C y).
    apply ct_to_lt_reduction; assumption. apply ct_to_lt_reduction; assumption.
  Defined.    

  Section abstraction_elimination_for_combinators.

    Variable A:Set.

    (** We present an optimized abstraction operator for combinators: terms built by it 
     are smaller than the naive usual implementation. In addition, it allows to build an
     inverse for the map ct_to_lt.*)

    Fixpoint ct_substitution (X Y:Set) (env: X -> C_Term Y) (f:C_Term X)
             {struct f}:C_Term Y:=
      match f with
      |ct_var _ v => env v
      |ct_k _ => ct_k Y
      |ct_s _ => ct_s Y
      |ct_app _ g h => ct_app Y (ct_substitution X Y env g) (ct_substitution X Y env h)
      end.
    
    Definition ct_specify (x:C_Term (option A)) (t:C_Term A):C_Term A:=
      ct_substitution
        (option A) A
        (fun x:option A => match x with |Some y => ct_var A y |None => t end)
        x.
    
    Inductive constant_combinator: C_Term (option A) -> Prop:=
    |cct_var: forall (i:A), constant_combinator (ct_var (option A) (Some i))
    |cct_k: constant_combinator (ct_k (option A))
    |cct_s: constant_combinator (ct_s (option A))
    |cct_app: forall y z:C_Term (option A),
        constant_combinator y -> constant_combinator z ->
        constant_combinator (ct_app (option A) y z).

    Fixpoint ct_specify_constant
             (x:C_Term (option A)) (cc: constant_combinator x) {struct cc}:
      forall s t:C_Term A, ct_specify x s = ct_specify x t.
    Proof.
      unfold ct_specify.
      destruct cc.
      intros; simpl; reflexivity.
      intros; simpl; reflexivity.
      intros; simpl; reflexivity.
      intros; simpl; apply f_equal2.
      apply ct_specify_constant; assumption.
      apply ct_specify_constant; assumption.
    Defined.
    
    Fixpoint cct_test (x:C_Term (option A)) {struct x}:
      sumbool (constant_combinator x) (~constant_combinator x).
    Proof.
      destruct x.      
      simpl. destruct o. left; apply cct_var.
      right; intro; inversion H.
      left; apply cct_k.
      left; apply cct_s.
      destruct cct_test with (x:=x1) as [l1|r1].
      destruct cct_test with (x:=x2) as [l2|r2].
      left; apply cct_app; assumption.
      right; intro; inversion H; contradiction.
      right; intro; inversion H; contradiction.
    Defined.      

    Fixpoint ct_abs (x:C_Term (option A)) {struct x}:C_Term A:=
      match x with
      |ct_app _ y z =>
       match (cct_test y) with        
       |left _ => match (cct_test z) with
                  |left _ => ct_app A (ct_k A) (ct_specify x (ct_k A))
                  |right _ => match z with
                              |ct_var _ j => (ct_specify y (ct_k A))
                              |ct_k _ => ct_app A (ct_k A) (ct_specify x (ct_k A))
                              |ct_s _ => ct_app A (ct_k A) (ct_specify x (ct_k A))
                              |ct_app _ _ _ =>
                               ct_app A (ct_app A (ct_s A) (ct_abs y)) (ct_abs z) 
                              end
                  end
       |right _ => ct_app A (ct_app A (ct_s A) (ct_abs y)) (ct_abs z)
       end
      |ct_var _ o => match o with
                     |None => ct_i A
                     |Some j => ct_app A (ct_k A) (ct_var A j) 
                     end
      |ct_k _ => ct_app A (ct_k A) (ct_specify x (ct_k A))
      |ct_s _ => ct_app A (ct_k A) (ct_specify x (ct_k A))                            
      end.

    Definition ct_specify_app: forall (p q:C_Term (option A)) (t:C_Term A),
        ct_specify (ct_app (option A) p q) t = ct_app A (ct_specify p t) (ct_specify q t).
    Proof.
      unfold ct_specify; simpl; reflexivity.
    Defined.
    
    Definition cwr_redex (x:C_Term (option A)) (t:C_Term A):
      ct_weak_reduction A (ct_app A (ct_abs x) t) (ct_specify x t).
    Proof.
      induction x.
      simpl. destruct a.
      apply cwr_k. apply cwr_i. simpl; apply cwr_k. simpl; apply cwr_k.
      simpl.
      destruct (cct_test x1).
      destruct (cct_test x2).
      fold ct_specify.
      rewrite ct_specify_constant with (s:=t) (t:=ct_k A).
      simpl. apply cwr_k.
      apply cct_app. assumption. assumption.
      destruct x2. rewrite ct_specify_app.
      destruct o. apply False_rect. apply n. apply cct_var.
      rewrite ct_specify_constant with (s:=t) (t:=ct_k A).
      unfold ct_specify; simpl; apply cwr_reflexivity. assumption.
      rewrite ct_specify_app.
      apply False_rect. apply n. apply cct_k.
      apply False_rect. apply n. apply cct_s.
      rewrite ct_specify_app.
      apply cwr_transitivity with
          (y:= ct_app A (ct_app A (ct_abs x1) t)
                      (ct_app A (ct_abs (ct_app (option A) x2_1 x2_2)) t)).
      apply cwr_s. apply cwr_app. apply IHx1. apply IHx2.
      rewrite ct_specify_app.
      apply cwr_transitivity with
          (y:= ct_app A (ct_app A (ct_abs x1) t) (ct_app A (ct_abs x2) t)).
      apply cwr_s. apply cwr_app. apply IHx1. apply IHx2.
    Defined.       
    
  End abstraction_elimination_for_combinators.

  Fixpoint ct_reduction_substitution
           (A B:Set) (env: A -> C_Term B)
           (x y:C_Term A) (w: ct_weak_reduction A x y) {struct w}:
    (ct_weak_reduction B (ct_substitution A B env x) (ct_substitution A B env y)).
  Proof.
    destruct w.
    simpl; apply cwr_k. simpl; apply cwr_s.
    simpl; apply cwr_app.
    apply ct_reduction_substitution; assumption.
    apply ct_reduction_substitution; assumption.
    apply cwr_reflexivity.
    apply cwr_transitivity with (y:= ct_substitution A B env y).
    apply ct_reduction_substitution; assumption.
    apply ct_reduction_substitution; assumption.
  Defined.

  Fixpoint lt_to_c (C:Set) (f:Lambda_Term C) {struct f}:
    C_Term C:=    
    match f with
    |lt_var _ j => ct_var C j 
    |lt_app _ a b => ct_app C (lt_to_c C a) (lt_to_c C b)
    |lt_abs _ g => ct_abs C (lt_to_c (option C) g)
    end.  

  Definition ct_to_lt_to_ct_inverse_identity:
    forall (C:Set) (x:C_Term C),
      lt_to_c C (ct_to_lt C x) = x.
  Proof.
    induction x.
    simpl; reflexivity.
    simpl; reflexivity.
    simpl; reflexivity.
    simpl; rewrite IHx1; rewrite IHx2; reflexivity.
  Defined.      

End elementary_combinators.

