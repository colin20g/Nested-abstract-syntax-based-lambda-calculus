Require Import NasLC.nested_abstract_syntax_lambda_calculus.

(** This text proves the confluence of the lambda calculus with the method of parallel 
    reductions invented by Masako Takahashi. We deal with beta eta reduction. 
 The simpler other reductions have obviously the same proof but shorter. *)

Section Takahashi_reductions_and_their_confluence.

  Notation T:= Lambda_Term.
  Notation V:= lt_var.
  Notation A:= lt_app.
  Notation L:= lt_abs.
  Notation "^ C":= (option C) (right associativity, at level 41).
  
  Inductive parallel_beta_eta_direct_reduction (C:Set): T C -> T C -> Set:=
  |pbed_var_refl: forall (x:C), parallel_beta_eta_direct_reduction C (V C x) (V C x)
  |pbed_app: forall (a a' b b':T C),
      parallel_beta_eta_direct_reduction C a a' ->
      parallel_beta_eta_direct_reduction C b b' ->
      parallel_beta_eta_direct_reduction C (A C a b) (A C a' b')
  |pbed_abs: forall (f f':T (^C)),
      parallel_beta_eta_direct_reduction (^C) f f' ->
      parallel_beta_eta_direct_reduction C (L C f) (L C f')
  |pbed_beta: forall (f f':T (^C)) (x x':T C),
      parallel_beta_eta_direct_reduction (^C) f f' ->
      parallel_beta_eta_direct_reduction C x x' ->
      parallel_beta_eta_direct_reduction C (A C (L C f) x) (lt_specify_new_var C f' x')
  |pbed_eta: forall (f f':T C),
      parallel_beta_eta_direct_reduction C f f' ->
      parallel_beta_eta_direct_reduction
        C
        (L C (A (^C) (lt_constant_embedding C f) (V (^C) None)))
        f'.

  Inductive parallel_beta_eta_reduction (C:Set): T C -> T C -> Set:=
  |pbe_refl: forall (x: T C), parallel_beta_eta_reduction C x x
  |pbe_step: forall (x y z:T C),
      parallel_beta_eta_reduction C x y ->
      parallel_beta_eta_direct_reduction C y z ->
      parallel_beta_eta_reduction C x z.

  Fixpoint pbed_refl (C:Set) (x:T C) {struct x}: parallel_beta_eta_direct_reduction C x x:=
    match x as l return (parallel_beta_eta_direct_reduction C l l) with
    | V _ c => pbed_var_refl C c
    | A _ x1 x2 => pbed_app C x1 x1 x2 x2 (pbed_refl C x1) (pbed_refl C x2)
    | L _ x0 => pbed_abs C x0 x0 (pbed_refl (^ C) x0)
    end.

  Notation "a §[ C ] b":= (parallel_beta_eta_direct_reduction C a b) (at level 49).
  Notation "a §*[ C ] b":= (parallel_beta_eta_reduction C a b) (at level 49).
  
  Section Takahashi_reduction_with_change_of_variables_and_substitution.

    Definition lt_constant_embedding_cov (C D:Set) (env: C -> D)
               (f: T C):
      lt_change_of_variables (^C) (lt_constant_embedding C f) (^D) (option_map env) =
      lt_constant_embedding D (lt_change_of_variables C f D env).
    Proof.
      unfold lt_constant_embedding. repeat rewrite lt_cov_composition_equality.
      simpl; reflexivity.
    Defined.
    
    Definition pbed_cov (C:Set) (x y:T C) (r: x §[C] y):
      forall (D:Set) (env: C -> D),
      (lt_change_of_variables C x D env) §[D] (lt_change_of_variables C y D env).
    Proof.
      induction r. intros; simpl; apply pbed_var_refl.
      intros; simpl; apply pbed_app. apply IHr1. apply IHr2.
      intros; simpl; apply pbed_abs; apply IHr.
      intros. rewrite lt_specify_new_var_cov. simpl. apply pbed_beta. apply IHr1. apply IHr2.
      intros. simpl; rewrite lt_constant_embedding_cov. apply pbed_eta; apply IHr.
    Defined.

    Notation ce:= (lt_constant_embedding).
    
    Definition pbed_ce (C:Set) (x y:T C) (r: x §[C] y): (ce C x) §[^C] (ce C y):=
      pbed_cov C x y r (^ C) Some.

    Definition lt_constant_embedding_sub (C D:Set) (env: C -> T D)
               (f: T C):
      lt_substitution (^C) (lt_constant_embedding C f) (^D) (lt_extend_environment C D env) =
      lt_constant_embedding D (lt_substitution C f D env).
    Proof.
      unfold lt_constant_embedding. unfold lt_extend_environment.
      rewrite lt_sub_after_cov_equality. rewrite lt_cov_after_sub_equality.
      apply lt_sub_pointwise_equality. unfold lt_constant_embedding; intro; reflexivity.
    Defined.
    
    Definition pbed_sub (C:Set) (x y:T C) (r: x §[C] y):
      forall (D:Set) (env1 env2: C -> T D) (redenv: forall i:C, env1 i §[D] env2 i),
      (lt_substitution C x D env1) §[D] (lt_substitution C y D env2).
    Proof.
      induction r. intros; simpl; apply redenv. intros; simpl; apply pbed_app.
      apply IHr1; assumption. apply IHr2; assumption.
      intros; simpl; apply pbed_abs; apply IHr. intros. destruct i.
      simpl; apply pbed_ce; apply redenv. simpl; apply pbed_var_refl.
      intros. rewrite lt_specify_new_var_sub. simpl. apply pbed_beta. apply IHr1.
      intros. destruct i. simpl; apply pbed_ce; apply redenv. simpl; apply pbed_var_refl.
      apply IHr2; assumption.
      intros. simpl. rewrite lt_constant_embedding_sub. apply pbed_eta. apply IHr; assumption.
    Defined.      

    Definition pbed_specify_new_var (C:Set) (f f': T (^C)) (x x':T C):
      f §[^C] f' -> x §[C] x' -> lt_specify_new_var C f x §[C] lt_specify_new_var C f' x'.
    Proof.
      intros; unfold lt_specify_new_var; apply pbed_sub. assumption.
      intros; destruct i; simpl. apply pbed_var_refl. assumption.
    Defined.      
      
  End Takahashi_reduction_with_change_of_variables_and_substitution.
  
  Section the_maximum_direct_reduction_operator.


    Section free_new_variables_and_constant_terms_characterizations.
      
      Fixpoint lt_free_variable_test (C:Set) (x:T C) {struct x}:
        forall (v:C) (eqv: forall w:C, sumbool (v = w) (v <> w)),
          sumbool (lt_free_variable C v x) (~ lt_free_variable C v x).
      Proof.
        destruct x. intros. destruct (eqv c). rewrite e. left; apply ltfv_atom.
        right. intro F. inversion F. contradiction.
        intros. destruct (lt_free_variable_test C x1 v eqv) as [y1|n1]. left.
        apply ltfv_app_left; assumption.
        destruct (lt_free_variable_test C x2 v eqv) as [y2|n2]. left.
        apply ltfv_app_right; assumption. right. intro F. inversion F; contradiction.
        intros. destruct lt_free_variable_test with (C:=^C) (x:=x) (v:= Some v) as [y|n].
        intros. destruct w. destruct (eqv c). rewrite e; left; reflexivity. right.
        intro F. inversion F; contradiction. right; discriminate.
        left; apply ltfv_abs; assumption. right; intro F; inversion F; contradiction.
      Defined.

      Definition non_constant (C:Set) (x:T (^C)):= lt_free_variable (^C) None x.

      Definition non_constant_test (C:Set) (x:T (^C)):
        sumbool (lt_free_variable (^C) None x) (~lt_free_variable (^C) None x).
      Proof.
        apply lt_free_variable_test. intros. destruct w. right; discriminate.
        left; reflexivity.
      Defined.

      Definition lt_i (C:Set):T C:= L C (V (^C) None).

      Definition lt_constant_value (C:Set) (f: T (^C)): T C:=
        lt_substitution (^C) f C (option_rect (fun _:^C => T C) (lt_var C) (lt_i C)).

      Definition lt_constant_value_cov (C D:Set) (env: C -> D) (f: T (^C)):
        lt_change_of_variables C (lt_constant_value C f) D env = 
        lt_constant_value D (lt_change_of_variables (^C) f (^D) (option_map env)).
      Proof.
        unfold lt_constant_value. rewrite lt_sub_after_cov_equality.
        rewrite lt_cov_after_sub_equality. apply lt_sub_pointwise_equality.
        intros. destruct i; simpl; reflexivity.
      Defined.
        
      Definition lt_constant_value_constant_embedding_equality (C:Set) (x: T C):
        lt_constant_value C (lt_constant_embedding C x) = x.
      Proof.
        unfold lt_constant_value. unfold lt_constant_embedding.
        rewrite lt_sub_after_cov_equality. simpl. apply lt_sub_identity_equality.
      Defined.

      Definition lt_sub_free_variable_pointwise_equality:
        forall (C : Set) (f : T C) (D : Set) (env1 env2 : C -> T D),
          (forall i : C, lt_free_variable C i f -> env1 i = env2 i) ->
          lt_substitution C f D env1 = lt_substitution C f D env2.
      Proof.
        induction f. intros. simpl. apply H. apply ltfv_atom.
        intros. simpl. rewrite IHf1 with (env2 := env2). rewrite IHf2 with (env2 := env2).
        reflexivity. intros. apply H. apply ltfv_app_right; assumption.
        intros. apply H. apply ltfv_app_left; assumption.
        intros. simpl. apply f_equal. apply IHf. intros. destruct i. simpl. apply f_equal.
        apply H. apply ltfv_abs; assumption. simpl; reflexivity.
      Defined.
        
      Definition lt_constant_embedding_constant_value_equality (C:Set) (y: T (^C)):
        ~non_constant C y ->
        lt_constant_embedding C (lt_constant_value C y) = y.
      Proof.
        unfold lt_constant_value. unfold lt_constant_embedding. unfold non_constant.
        rewrite lt_cov_after_sub_equality. intro.
        rewrite lt_sub_free_variable_pointwise_equality with (env2 := lt_var (^C)).
        apply lt_sub_identity_equality. intros. destruct i. simpl; reflexivity. contradiction.
      Defined.

      Lemma already_present_letters_cov (C:Set) (f: T C):
        forall (D:Set) (env: C -> D) (w:D),
          lt_free_variable D w (lt_change_of_variables C f D env) ->
          exists v:C, (lt_free_variable C v f) /\ (env v = w).
      Proof.
        induction f. intros. inversion H. exists c. split. apply ltfv_atom. reflexivity.
        simpl. intros. inversion H. apply IHf1 in H1. destruct H1 as (v1,pv1).
        exists v1. split. apply ltfv_app_left; apply pv1. apply pv1.
        apply IHf2 in H1. destruct H1 as (v2,pv2).
        exists v2. split. apply ltfv_app_right; apply pv2. apply pv2.
        simpl. intros. inversion H.  apply IHf in H1. destruct H1 as (o,po).
        destruct po as (pol, por). destruct o. exists c. split. apply ltfv_abs; apply pol.
        inversion por; reflexivity.  simpl in por; inversion por.
      Defined.
        
      Definition lt_constant_embedding_is_constant (C:Set) (f: T C):
        ~non_constant C (lt_constant_embedding C f).
      Proof.
        unfold non_constant. unfold lt_constant_embedding. intro F.
        apply already_present_letters_cov in F. destruct F as (L,R). destruct R as (P,Q).
        inversion Q.
      Defined.      

      Definition lt_free_variable_cov (C:Set) (v:C) (f:T C)
                 (p:lt_free_variable C v f): forall (D:Set) (env: C -> D),
          lt_free_variable D (env v) (lt_change_of_variables C f D env).
      Proof.
        induction p. simpl; intros; apply ltfv_atom.
        simpl; intros; apply ltfv_app_left; apply IHp; assumption.
        simpl; intros; apply ltfv_app_right; apply IHp; assumption.
        simpl; intros; apply ltfv_abs. apply IHp with (env := option_map env).
      Defined.

      Definition non_constant_cov (C D:Set) (env: C -> D) (f: T (^C)):
        non_constant C f <->
        non_constant D (lt_change_of_variables (^C) f (^D) (option_map env)).
      Proof.
        unfold non_constant. split. intro p.
        apply lt_free_variable_cov with (D:= ^D) (env := option_map env) in p.
        simpl in p; assumption. intro q. destruct (non_constant_test C f) as [y|n].
        assumption. apply lt_constant_embedding_constant_value_equality in n.
        rewrite <- n in q. rewrite lt_constant_embedding_cov in q. 
        apply lt_constant_embedding_is_constant in q. contradiction.
      Defined.        

      Lemma already_present_letters_sub (C:Set) (f: T C):
        forall (D:Set) (env: C -> T D) (w:D),
          lt_free_variable D w (lt_substitution C f D env) ->
          exists i:C, (lt_free_variable C i f) /\(lt_free_variable D w (env i)).
      Proof.
        induction f. intros. exists c. split. apply ltfv_atom. simpl in H; assumption.
        intros. simpl in H. inversion H.
        apply IHf1 in H1. destruct H1 as (i1,p1). exists i1. split.
        apply ltfv_app_left; apply p1. apply p1.
        apply IHf2 in H1. destruct H1 as (i2,p2). exists i2. split.
        apply ltfv_app_right; apply p2. apply p2.
        intros. simpl in H. inversion H. apply IHf in H1.
        destruct H1 as (i,pi). destruct i. exists c. split. apply ltfv_abs. apply pi.
        simpl in pi. unfold lt_constant_embedding in pi.
        destruct pi as (pir, pil). apply already_present_letters_cov in pil.
        destruct pil as (iv, piv). destruct piv as (fiv, eiv). inversion eiv.
        rewrite H2 in fiv; assumption. simpl in pi. destruct pi as (X,F). inversion F.
      Defined.

      Definition free_letters_in_specify_new_var (C:Set) (f:T (^C)) (t:T C) (v:C):
        lt_free_variable C v (lt_specify_new_var C f t) ->
        (lt_free_variable C v t) \/ (lt_free_variable (^C) (Some v) f).
      Proof.
        unfold lt_specify_new_var. unfold lt_set_new_variable. intro P.
        apply already_present_letters_sub in P.
        destruct P as (o, po). destruct po as (pol, por). destruct o. right. inversion por.
        assumption. left; assumption.
      Defined.
      
    End free_new_variables_and_constant_terms_characterizations.    
    
    Fixpoint max_pbed (C:Set) (x:T C) {struct x}: T C:=
      match x as l return T C with
      |V _ c => V _ c
      |A _ y z => match y with
                  | L _ f => lt_specify_new_var C (max_pbed (^C) f) (max_pbed C z)
                  | _ => A C (max_pbed C y) (max_pbed C z)
                  end
      |L _ g => match g with
                | A _ h (V _ None) => match (non_constant_test C h) with
                                            | left _ => L C (max_pbed (^C) g)
                                            | right _ =>
                                              lt_constant_value C (max_pbed (^C) h)
                                            end
                | _ => L C (max_pbed (^C) g) 
                end 
      end.

    Lemma lt_app_cov (C:Set) (f g:T C) (D:Set) (env: C -> D):
        lt_change_of_variables C (A C f g) D env =
        A D (lt_change_of_variables C f D env) (lt_change_of_variables C g D env).
    Proof.
      simpl; reflexivity.
    Defined.
    
    Lemma lt_abs_cov (C:Set) (f:T (^C)) (D:Set) (env: C -> D):
      lt_change_of_variables C (L C f) D env =
      L D (lt_change_of_variables (^C) f (^D) (option_map env)).
    Proof.
      simpl; reflexivity.
    Defined.

    Fixpoint max_pbed_cov (C:Set) (f:T C) (D:Set) (env: C -> D) {struct f}:
        lt_change_of_variables C (max_pbed C f) D env =
        max_pbed D (lt_change_of_variables C f D env).
    Proof.
      destruct f. simpl; reflexivity.
      assert (lt_change_of_variables C (max_pbed C f1) D env =
              max_pbed D (lt_change_of_variables C f1 D env)) as R1. apply max_pbed_cov.
      assert (lt_change_of_variables C (max_pbed C f2) D env =
              max_pbed D (lt_change_of_variables C f2 D env)) as R2. apply max_pbed_cov.
      destruct f1. simpl. rewrite R2.
      reflexivity.
      assert (forall (U:Set) (p q r: T U), max_pbed U (A U (A U p q) r) =
                                           A U (max_pbed U (A U p q)) (max_pbed U r)
             ) as E. intros; simpl; reflexivity. rewrite E. repeat rewrite lt_app_cov.
      rewrite R1. rewrite E. rewrite lt_app_cov. rewrite R2. reflexivity.
      simpl. rewrite lt_specify_new_var_cov. apply f_equal2. apply max_pbed_cov. apply R2.
      assert (lt_change_of_variables (^C) (max_pbed (^C) f )(^D) (option_map env) =
              max_pbed (^D) (lt_change_of_variables (^C) f (^D) (option_map env))
             ) as R. apply max_pbed_cov.
      destruct f. simpl; reflexivity. destruct f2. destruct o.
      simpl; simpl in R; rewrite R. reflexivity. rewrite lt_abs_cov. rewrite lt_app_cov.
      assert (lt_change_of_variables (^C) (V (^C) None) (^D) (option_map env)
              = V (^D) None) as ENone. simpl; reflexivity. rewrite ENone.
      simpl.
      destruct (non_constant_test C f1).
      destruct (non_constant_test D (lt_change_of_variables (^C) f1 (^D) (option_map env))).
      simpl in R. rewrite <- R. rewrite lt_abs_cov. reflexivity. apply False_ind.
      apply n. apply non_constant_cov. assumption.
      destruct (non_constant_test D (lt_change_of_variables (^C) f1 (^D) (option_map env))).
      apply False_ind. apply n. apply non_constant_cov in l. assumption.
      rewrite lt_constant_value_cov. apply f_equal; apply max_pbed_cov.
      simpl; simpl in R; rewrite R; reflexivity.
      simpl; simpl in R; rewrite R; reflexivity.
      simpl; simpl in R; rewrite R; reflexivity.
    Defined.

    Definition max_pbed_ce (C:Set) (x:T C):
      lt_constant_embedding C (max_pbed C x) =
      max_pbed (^C) (lt_constant_embedding C x).
    Proof.
      unfold lt_constant_embedding; apply max_pbed_cov.
    Defined.
    
    Fixpoint pbed_towards_max (C:Set) (x:T C) {struct x}:
      x §[C] max_pbed C x.
    Proof.
      destruct x. simpl; apply pbed_var_refl. simpl.
      assert (x1 §[C] max_pbed C x1) as R1. apply pbed_towards_max.
      assert (x2 §[C] max_pbed C x2) as R2. apply pbed_towards_max.
      destruct x1. apply pbed_app. simpl; apply pbed_refl. assumption.
      apply pbed_app; assumption. apply pbed_beta. apply pbed_towards_max. assumption.
      assert (x §[^C] max_pbed (^C) x) as R. apply pbed_towards_max.
      destruct x. simpl; apply pbed_refl. destruct x2. destruct o.
      simpl. apply pbed_abs. simpl in R. assumption. simpl.
      destruct (non_constant_test C x1). simpl in R. apply pbed_abs; assumption.
      assert (L C (A (^C) x1 (V (^C) None)) =
              L C (A (^C) (lt_constant_embedding C (lt_constant_value C x1)) (V (^C) None))
             ) as Ecvce.
      rewrite <- lt_constant_embedding_constant_value_equality with (y:=x1).
      rewrite lt_constant_value_constant_embedding_equality. reflexivity. assumption.
      rewrite Ecvce. apply pbed_eta. unfold lt_constant_value. apply pbed_sub.
      apply pbed_towards_max. intros. apply pbed_refl. 
      simpl. apply pbed_abs. simpl in R. assumption.
      simpl. apply pbed_abs. simpl in R. assumption.
      simpl. apply pbed_abs. simpl in R. assumption.
    Defined.                   
    
  End the_maximum_direct_reduction_operator.

  Lemma lt_app_sub (C:Set) (f g:T C) (D:Set) (env: C -> T D):
    lt_substitution C (A C f g) D env =
    A D (lt_substitution C f D env) (lt_substitution C g D env).
  Proof.
    simpl; reflexivity.
  Defined.

  Lemma lt_app_specify_new_var (C:Set) (f g:T (^ C)) (t:T C):
    lt_specify_new_var C (A (^C) f g) t =
    A C (lt_specify_new_var C f t) (lt_specify_new_var C g t).
  Proof.
    apply lt_app_sub. 
  Defined.  

  Fixpoint no_letter_added_by_reduction
           (C:Set) (x y:T C) (r: x§[C] y) {struct r}:
    forall (v:C), lt_free_variable C v y -> lt_free_variable C v x.
  Proof.
    destruct r. intros. assumption. intros v Fv. inversion Fv.
    apply ltfv_app_left. apply no_letter_added_by_reduction with (v:=v) in r1; assumption.
    apply ltfv_app_right. apply no_letter_added_by_reduction with (v:=v) in r2; assumption.
    intros v Fv. inversion Fv.
    apply ltfv_abs; apply no_letter_added_by_reduction with (v:= Some v) in r; assumption.
    intros v Fv. apply free_letters_in_specify_new_var in Fv.
    destruct Fv as [Fvl|Fvr]. apply no_letter_added_by_reduction with (v:=v) in r2.
    apply ltfv_app_right. assumption. assumption.
    apply no_letter_added_by_reduction with (v:=Some v) in r1. apply ltfv_app_left.
    apply ltfv_abs; assumption. assumption.
    intros v Fv. apply no_letter_added_by_reduction with (v:=v) in r.
    apply ltfv_abs. apply ltfv_app_left. unfold lt_constant_embedding.
    apply lt_free_variable_cov. assumption. assumption.
  Defined.  

  Corollary reduction_of_constants (C:Set) (x y: T (^C)):
    (~ non_constant C x) ->
    x §[^C] y ->
    ~ non_constant C y.
  Proof.
    unfold non_constant. intros. intro. apply H.
    apply no_letter_added_by_reduction with (v:= None) in H0; assumption.
  Defined.
  
  Fixpoint Takahashi_confluence_trick (C:Set) (f: T C) {struct f}:
    forall (g: T C), f §[C] g ->
                     g §[C] max_pbed C f.
  Proof.
    destruct f. intros g R. inversion R. simpl; apply pbed_var_refl. 
    assert (forall k:T C, f1 §[C] k -> k §[C] max_pbed C f1) as Q1.
    apply Takahashi_confluence_trick; assumption.
    assert (forall k:T C, f2 §[C] k -> k §[C] max_pbed C f2) as Q2.
    apply Takahashi_confluence_trick; assumption. intros g R. inversion R.
    destruct f1. simpl. apply pbed_app. apply Q1; assumption. simpl. apply Q2; assumption.
    simpl. destruct f1_1. inversion H1.
    apply pbed_app. apply Q1. rewrite H7; assumption. apply Q2; assumption. apply pbed_app.
    apply Q1; assumption. apply Q2; assumption.
    apply pbed_app. apply Q1; assumption. apply Q2; assumption.
    assert (forall k:T (^C), f1 §[^C] k -> k §[^C] max_pbed (^C) f1) as Q1'.
    apply Takahashi_confluence_trick; assumption. simpl. inversion H1.
    apply pbed_beta. apply Q1'; assumption. apply Q2; assumption.
    assert (A C a' b' = lt_specify_new_var C (A (^C) (lt_constant_embedding C a')
                                                (V (^C) None)) b') as Ea'.
    rewrite lt_app_specify_new_var. rewrite lt_specify_new_var_constant.
    unfold lt_specify_new_var; simpl; reflexivity. rewrite Ea'. apply pbed_specify_new_var.
    rewrite <- H4 in Q1'. apply Q1'. apply pbed_app. apply pbed_cov; assumption.
    apply pbed_var_refl. apply Q2; assumption. simpl.
    apply pbed_specify_new_var.
    destruct f1. inversion H. inversion H. 
    assert (forall k:T (^C), f1 §[^C] k -> k §[^C] max_pbed (^C) f1) as Q.
    apply Takahashi_confluence_trick. inversion H. rewrite H5 in H1. apply Q in H1.
    assumption. apply Q2; assumption.
    intros. 
    assert (forall k:T (^C), f §[^C] k -> k §[^C] max_pbed (^C) f) as Q'.
    apply Takahashi_confluence_trick.
    destruct f. simpl. inversion H. inversion H1. apply pbed_refl. 
    assert (forall k:T (^C), f1 §[^C] k -> k §[^C] max_pbed (^C) f1) as Q1'.
    apply Takahashi_confluence_trick.
    assert (forall k:T (^C), f2 §[^C] k -> k §[^C] max_pbed (^C) f2) as Q2'.
    apply Takahashi_confluence_trick.
    destruct f2. destruct o. inversion H. simpl. apply pbed_abs; apply Q'; assumption.
    simpl. destruct (non_constant_test C f1).
    inversion H. simpl. apply pbed_abs; apply Q'; assumption.
    apply False_rect. apply (lt_constant_embedding_is_constant C f). rewrite <- H0 in l.
    assumption. destruct f1.    
    inversion H. inversion H1. inversion H5. inversion H7. unfold lt_constant_value.
    destruct o. simpl. apply pbed_eta with (f:= V C c). apply pbed_refl. simpl.
    apply False_rect. apply n. apply ltfv_atom. rewrite H0.
    apply f_equal with (f:= lt_constant_value C) in H0.
    rewrite lt_constant_value_constant_embedding_equality in H0. rewrite H0 in H1.
    destruct o. unfold lt_constant_value. unfold lt_constant_value in H1. simpl in H1.
    simpl. inversion H1; apply pbed_var_refl. apply False_rect. apply n; apply ltfv_atom.
    assert (forall k:T (^C), f1_1 §[^C] k -> k §[^C] max_pbed (^C) f1_1) as Q1_1'.
    apply Takahashi_confluence_trick.
    assert (forall k:T (^C), f1_2 §[^C] k -> k §[^C] max_pbed (^C) f1_2) as Q1_2'.
    apply Takahashi_confluence_trick. inversion H. inversion H1. inversion H7.
    assert (lt_constant_embedding C (lt_constant_value C a') = a') as Ea'.
    apply lt_constant_embedding_constant_value_equality.
    apply reduction_of_constants with (x:= A (^C) f1_1 f1_2); assumption. rewrite <- Ea'.
    apply pbed_eta. unfold lt_constant_value; apply pbed_sub. apply Q1'. assumption.
    intros; apply pbed_refl.
    apply pbed_ce in H1. rewrite H0 in H1. apply Q1' in H1. 
    rewrite <- lt_constant_value_constant_embedding_equality with (x:= g).
    unfold lt_constant_value; apply pbed_sub. rewrite H0; assumption. intros; apply pbed_refl.
    assert (forall k:T (^^C), f1 §[^^C] k -> k §[^^C] max_pbed (^^C) f1) as Q1''.
    apply Takahashi_confluence_trick. inversion H. inversion H1. inversion H7. 
    assert (lt_constant_embedding C (lt_constant_value C a') = a') as Ea'.
    apply lt_constant_embedding_constant_value_equality.
    apply reduction_of_constants with (x:= L (^C) f1); assumption. rewrite <- Ea'.
    apply pbed_eta. unfold lt_constant_value; apply pbed_sub. apply Q1'. assumption.
    intros; apply pbed_refl. inversion H7.
    rewrite <- lt_constant_value_constant_embedding_equality with
        (x:= L C (lt_specify_new_var (^ C) f'0 (V (^ C) None))). unfold lt_constant_value.
    apply pbed_sub. apply Q1'. unfold lt_constant_embedding. simpl.
    apply pbed_abs. unfold lt_specify_new_var. rewrite lt_cov_after_sub_equality.
    assert (lt_substitution (^^C) f1 (^^C) (lt_var (^^C)) =
            lt_substitution
              (^^ C) f1 (^^ C)
              (fun i : ^^ C =>
                 lt_change_of_variables (^ C) (lt_set_new_variable (^ C) (V (^ C) None) i)
                                        (^ (^ C)) (option_map Some))
           ) as Ef1.
    apply lt_sub_free_variable_pointwise_equality. intros. destruct i.
    destruct o. simpl. reflexivity. apply False_rect. apply n. apply ltfv_abs; assumption.
    simpl; reflexivity. rewrite lt_sub_identity_equality in Ef1. rewrite Ef1. apply pbed_sub.
    assumption. intros; apply pbed_refl. intros; apply pbed_refl. 
    apply pbed_ce in H1. rewrite H0 in H1. apply Q1' in H1. 
    rewrite <- lt_constant_value_constant_embedding_equality with (x:= g).
    unfold lt_constant_value; apply pbed_sub. rewrite H0; assumption. intros; apply pbed_refl.
    inversion H. simpl. apply pbed_abs. apply Q'; assumption.
    inversion H. simpl. apply pbed_abs. apply Q'; assumption. 
    inversion H. simpl. apply pbed_abs. apply Q'; assumption.
  Defined.

  Definition pbed_confluence (C:Set) (x a b:T C):
    (x §[C] a) -> (x§[C] b) -> {y:T C & prod (a §[C] y) (b §[C] y)}.
  Proof.
    intros ra rb. exists (max_pbed C x). split; apply Takahashi_confluence_trick; assumption.
  Defined.  

  Fixpoint pbe_pbed_semi_confluence (C:Set) (x a:T C) (r: x §*[C] a) (b:T C) (s: x §[C] b)
           {struct r}:
     {y:T C & prod (a §[C] y) (b §*[C] y)}.
  Proof.
    destruct r. exists b. split. assumption. apply pbe_refl.
    apply pbe_pbed_semi_confluence with (b:=b) in r.
    destruct r as (w,pw). apply pbed_confluence with (b:= w) in p. destruct p as (v,pv).
    exists v. split. apply pv. apply pbe_step with (y:= w). apply pw. apply pv. apply pw.
    assumption.
  Defined.

  Fixpoint pbe_confluence (C:Set) (x a:T C) (r: x §*[C] a) (b:T C) (s: x §*[C] b)
           {struct r}:
     {y:T C & prod (a §*[C] y) (b §*[C] y)}.
  Proof.
    destruct r. exists b. split. assumption. apply pbe_refl.
    apply pbe_confluence with (b:=b) in r.
    destruct r as (w,pw). apply pbe_pbed_semi_confluence with (a:= w) in p.
    destruct p as (v,pv).
    exists v. split. apply pv. apply pbe_step with (y:= w). apply pw. apply pv. apply pw.
    assumption.
  Defined.
    
End Takahashi_reductions_and_their_confluence.

Section equivalence_between_Takahashi_and_usual_reduction_and_confluence_of_the_latter.

  Notation T:= Lambda_Term.
  Notation V:= lt_var.
  Notation A:= lt_app.
  Notation L:= lt_abs.
  Notation "^ C":= (option C) (right associativity, at level 41).

  Notation "a §[ C ] b":= (parallel_beta_eta_direct_reduction C a b) (at level 49).
  Notation "a §*[ C ] b":= (parallel_beta_eta_reduction C a b) (at level 49).

  Notation "a >[ C ] b":= (lt_beta_eta_reduction C a b) (at level 49).
  
  Section good_behavior_of_beta_eta_reduction_under_change_of_variables_and_substitution.

    Definition ltber_cov (C:Set) (x y:T C) (r: x >[C] y):
      forall (D:Set) (env: C -> D),
        (lt_change_of_variables C x D env) >[D] (lt_change_of_variables C y D env).
    Proof.
      induction r. intros; simpl; rewrite lt_specify_new_var_cov; apply ltber_redex.
      intros; simpl; rewrite lt_constant_embedding_cov; apply ltber_eta.
      intros; simpl; apply ltber_app. apply IHr1. apply IHr2.
      intros; simpl; apply ltber_abs; apply IHr. intros; apply ltber_reflexivity.
      intros; simpl; apply ltber_transitivity with (y:= lt_change_of_variables C y D env).
      apply IHr1. apply IHr2.
    Defined.

    Notation ce:= (lt_constant_embedding).
    
    Definition ltber_ce (C:Set) (x y:T C) (r: x >[C] y): (ce C x) >[^C] (ce C y):=
      ltber_cov C x y r (^ C) Some.
    
    Definition ltber_sub (C:Set) (x y:T C) (r: x >[C] y):
      forall (D:Set) (env: C -> T D),
        (lt_substitution C x D env) >[D] (lt_substitution C y D env).
    Proof.
      induction r. intros; simpl. rewrite lt_specify_new_var_sub; apply ltber_redex.
      intros. simpl. rewrite lt_constant_embedding_sub. apply ltber_eta.
      intros; simpl; apply ltber_app. apply IHr1; assumption. apply IHr2; assumption.
      intros; simpl; apply ltber_abs; apply IHr; assumption.
      intros; apply ltber_reflexivity.
      intros; simpl; apply ltber_transitivity with (y:= lt_substitution C y D env).
      apply IHr1. apply IHr2.
    Defined.

    Definition ltber_env (C:Set) (x:T C):
      forall (D:Set) (env1 env2: C -> T D) (redenv: forall i:C, env1 i >[D] env2 i),
        (lt_substitution C x D env1) >[D] (lt_substitution C x D env2).
    Proof.
      induction x. intros; simpl; apply redenv. intros; simpl; apply ltber_app.
      apply IHx1; assumption. apply IHx2; assumption.
      intros; simpl; apply ltber_abs; apply IHx. intros. destruct i.
      simpl; apply ltber_ce; apply redenv. simpl; apply ltber_reflexivity.
    Defined.
      
    Definition ltber_parallel_sub (C:Set) (x y:T C) (r: x >[C] y):
      forall (D:Set) (env1 env2: C -> T D) (redenv: forall i:C, env1 i >[D] env2 i),
        (lt_substitution C x D env1) >[D] (lt_substitution C y D env2).
    Proof.
      intros. apply ltber_transitivity with (y:= lt_substitution C y D env1).
      apply ltber_sub; assumption. apply ltber_env; apply redenv.
    Defined.
    
    Definition ltber_parallel_specify_new_var (C:Set) (f f': T (^C)) (x x':T C):
      f >[^C] f' -> x >[C] x' -> lt_specify_new_var C f x >[C] lt_specify_new_var C f' x'.
    Proof.
      intros; unfold lt_specify_new_var; apply ltber_parallel_sub. assumption.
      intros; destruct i; simpl. apply ltber_reflexivity. assumption.
    Defined.      

    Definition ltber_parallel_beta (C:Set) (f f':T (^C)) (x x':T C):
      f >[^C] f' -> x >[C] x' -> A C (L C f) x >[C] lt_specify_new_var C f' x'.
    Proof.
      intros; apply ltber_transitivity with (y:= lt_specify_new_var C f x).
      apply ltber_redex. apply ltber_parallel_specify_new_var; assumption.
    Defined.

    Definition ltber_parallel_eta (C:Set) (f f':T C):
      f >[C] f' -> L C (A (^C) (lt_constant_embedding C f) (V (^C) None)) >[C] f'.
    Proof.
      intros; apply ltber_transitivity with (y:= f). apply ltber_eta; assumption. assumption.
    Defined.
      
  End good_behavior_of_beta_eta_reduction_under_change_of_variables_and_substitution.
 
  Section further_properties_of_parallel_beta_eta_reduction.
    
    Definition pbed_to_pbe (C:Set) (x y:T C):
      x §[C] y -> x §*[C] y.
    Proof.
      intros. apply pbe_step with (y:=x). apply pbe_refl. assumption.
    Defined.

    Definition pbe_transitivity (C:Set) (y z:T C) (r: y §*[C] z):
      forall (x: T C), x §*[C] y -> x §*[C] z.
      induction r. intros; assumption. intros. apply pbe_step with (y:=y).
      apply IHr; assumption. assumption.
    Defined.

    Definition pbe_left (C:Set) (x a b:T C) (r: a §*[C] b):
      (A C a x) §*[C] (A C b x).
    Proof.
      induction r. apply pbe_refl. apply pbe_step with (y:= A C y x). assumption.
      apply pbed_app. assumption. apply pbed_refl.
    Defined.

    Definition pbe_right (C:Set) (x a b:T C) (r: a §*[C] b):
      (A C x a) §*[C] (A C x b).
    Proof.
      induction r. apply pbe_refl. apply pbe_step with (y:= A C x y). assumption.
      apply pbed_app. apply pbed_refl. assumption.
    Defined.
      
    Definition pbe_app (C:Set) (x x' y y':T C):
      x §*[C] x' -> y §*[C] y' -> (A C x y) §*[C] (A C x' y').
    Proof.
      intros. apply pbe_transitivity with (y:= A C x' y). apply pbe_right; assumption.
      apply pbe_left; assumption.
    Defined.

    Definition pbe_abs (C:Set) (x y:T (^C)) (r: x §*[^C] y):
      L C x §*[C] L C y.
    Proof.
      induction r. apply pbe_refl. apply pbe_step with (y:= L C y). assumption.
      apply pbed_abs. assumption.
    Defined.      
      
  End further_properties_of_parallel_beta_eta_reduction.
    
  Section equivalence_between_the_two_reductions.

    Ltac tr := apply pbed_to_pbe.

    Definition pbed_to_ltber (C:Set) (x y:T C) (r: parallel_beta_eta_direct_reduction C x y):
      lt_beta_eta_reduction C x y.
    Proof.
      induction r. apply ltber_reflexivity. apply ltber_app; assumption.
      apply ltber_abs; assumption. apply ltber_parallel_beta; assumption.
      apply ltber_parallel_eta; assumption.
    Defined.

    Definition pbe_to_ltber (C:Set) (x y:T C) (r: parallel_beta_eta_reduction C x y):
      lt_beta_eta_reduction C x y.
    Proof.
      induction r. apply ltber_reflexivity. apply ltber_transitivity with (y:=y).
      assumption. apply pbed_to_ltber; assumption.
    Defined.

    Definition ltber_to_pbe (C:Set) (x y:T C) (r: lt_beta_eta_reduction C x y):
      parallel_beta_eta_reduction C x y.      
    Proof.
      induction r. tr; apply pbed_beta; apply pbed_refl. tr; apply pbed_eta; apply pbed_refl. 
      apply pbe_app; assumption. apply pbe_abs; assumption. apply pbe_refl.
      apply pbe_transitivity with (y:= y); assumption.
    Defined.
            
  End equivalence_between_the_two_reductions.

  Section the_Church_Rosser_for_beta_eta_reduction_in_lambda_calculus.

    Definition ltber_confluence (C:Set) (x a:T C) (r: x >[C] a) (b:T C) (s: x >[C] b):
      {y:T C & prod (a >[C] y) (b >[C] y)}.
    Proof.
      apply ltber_to_pbe in r. apply ltber_to_pbe in s.
      destruct (pbe_confluence C x a r b s) as (m,p). exists m.
      split; apply pbe_to_ltber; apply p.
    Defined.    

  End the_Church_Rosser_for_beta_eta_reduction_in_lambda_calculus.  
  
End equivalence_between_Takahashi_and_usual_reduction_and_confluence_of_the_latter.
