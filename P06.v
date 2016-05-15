Require Export P05.
(*
Lemma replace_cequiv: forall (c1 c2:com),
  cequiv c1 (constfold_0plus c1) -> cequiv c2 (constfold_0plus c2) -> 
  cequiv ((constfold_0plus c1);; (constfold_0plus c2)) 
    (constfold_0plus (c1;; c2)).
Proof.
  intros.  
  unfold constfold_0plus. simpl.
  destruct c1.
  Case "c1=SKIP".
    simpl.
    assert (H1: cequiv (SKIP;; (constfold_0plus c2)) (SKIP;; c2)).
    apply CSeq_congruence. apply refl_cequiv. apply sym_cequiv. assumption.
    assert (H2: cequiv (SKIP;; c2) (optimize_0plus_com c2)).
    assert (H3: cequiv (SKIP;;c2) c2). 
    unfold cequiv. split. apply skip_left. apply skip_left.
    apply trans_cequiv with (c2:=c2). assumption. apply optimize_0plus_com_sound.
    unfold constfold_0plus in H1. apply trans_cequiv with (c2:=(SKIP;; c2)). assumption. assumption.
  Case "c1 = ::=".
    destruct c2. 
    SCase "c2 = SKIP". 
      assert (H1: cequiv ((i ::= a);;SKIP) ((constfold_0plus (i ::= a));; (constfold_0plus SKIP))).
        apply CSeq_congruence. assumption. assumption.
      assert (H2: cequiv ((i ::= a);;SKIP) (i ::= a)).
        apply skip_right.
      apply sym_cequiv in H1.
      apply trans_cequiv with (c2:=((i ::= a);; SKIP)).
      unfold constfold_0plus in H1. assumption.
      assert (H3: cequiv (i ::= a) (optimize_0plus_com (i ::= a))).
        apply optimize_0plus_com_sound.
      apply trans_cequiv with (c2:=(i ::= a)).
      assumption. assumption.
    SCase "c2 = ::=".
      simpl. apply refl_cequiv.
    SCase "c2 = ;;".
      simpl. destruct c2_1; 
        apply refl_cequiv;
        destruct c2_2; apply refl_cequiv.
          apply refl_cequiv.
          apply refl_cequiv.
  Case "c1 = ;;".
    destruct c2.
    SCase "c2 = SKIP". 
      simpl. destruct c1_1.
      SSCase "c1_1 = SKIP".
        assert (H1: cequiv (optimize_0plus_com c1_2;; SKIP) (optimize_0plus_com c1_2)).
          apply skip_right.
        assert (H2: cequiv (optimize_0plus_com c1_2) (optimize_0plus_com SKIP;; optimize_0plus_com c1_2)).
          assert (H3: cequiv (optimize_0plus_com SKIP;; optimize_0plus_com c1_2)
            (SKIP;; optimize_0plus_com c1_2)).
            apply CSeq_congruence. apply sym_cequiv in H0. assumption. apply refl_cequiv.
        assert (H4: cequiv (SKIP;; optimize_0plus_com c1_2) (optimize_0plus_com c1_2)).
          apply skip_left.
        apply sym_cequiv. apply trans_cequiv with (c2:= (SKIP;; optimize_0plus_com c1_2)).
        assumption. assumption.
        apply trans_cequiv with (c2:=(optimize_0plus_com c1_2)).
        assumption. assumption.
      SSCase "c1_1 = :=".
        destruct c1_2.
          simpl. apply refl_cequiv.
          simpl. apply CSeq_congruence.
*)

Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
  unfold ctrans_sound. intros c.
  induction c.
  Case "SKIP".
    unfold constfold_0plus. simpl. apply refl_cequiv.
  Case "::=".
    apply CAss_congruence. unfold aequiv. intro st.
    induction a; try auto; 
      simpl; destruct (fold_constants_aexp a1); destruct (fold_constants_aexp a2);
        try (rewrite IHa1; rewrite IHa2; auto); try destruct n; auto.
  Case ";;".
    destruct c1.
    SCase "c1 = SKIP".
      unfold constfold_0plus in IHc2.
      assert (H:cequiv c2 (fold_constants_com c2)).
      apply fold_constants_com_sound. 
      assert (H1: cequiv (SKIP;;c2) c2). 
      unfold cequiv. split. apply skip_left. apply skip_left. 
      apply trans_cequiv with (c2:=c2). assumption. apply optimize_0plus_com_sound. 
    SCase "c1 = ::=".
    destruct c2. 
      SSCase "c2 = SKIP". 
      assert (H1: cequiv ((i ::= a);;SKIP) ((constfold_0plus (i ::= a));; (constfold_0plus SKIP))).
        apply CSeq_congruence. assumption. assumption.
      assert (H2: cequiv ((i ::= a);;SKIP) (i ::= a)).
        apply skip_right.
      apply sym_cequiv in H1.
      apply trans_cequiv with (c2:=((i ::= a);; SKIP)).
      unfold constfold_0plus in H1. apply refl_cequiv.
      assert (H3: cequiv (i ::= a) (optimize_0plus_com (i ::= a))).
        apply optimize_0plus_com_sound.
      apply trans_cequiv with (c2:=(i ::= a)).
      assumption. assumption.
      SSCase "c2 = ::=".
        unfold constfold_0plus. simpl. unfold constfold_0plus in *.
        apply CSeq_congruence. assumption. assumption.
      SSCase "c2 = ;;".
        unfold constfold_0plus. simpl.
        destruct c2_1.
        SSSCase "c2_1 = SKIP".
          simpl. 
          assert (H: cequiv (SKIP;; c2_2) (optimize_0plus_com c2_2)).
           assert (H1:  cequiv (SKIP;; c2_2) c2_2). apply skip_left.
           assert (H2: cequiv c2_2 (optimize_0plus_com c2_2)). apply optimize_0plus_com_sound.
           apply trans_cequiv with (c2:=c2_2). assumption. assumption.
          apply CSeq_congruence. unfold constfold_0plus in IHc1. assumption. assumption.
        SSSCase "c2_1 = ::=".
          destruct c2_2.
          SSSSCase "c2_2 = SKIP".
            assert (H: cequiv (i0 ::= a0;; SKIP) (i0 ::= a0)).
              apply skip_right.
            assert (H1: cequiv (i0 ::= a0) (optimize_0plus_com (i0 ::= a0))).
              apply optimize_0plus_com_sound.
            apply CSeq_congruence. unfold constfold_0plus in IHc1. assumption.
            apply trans_cequiv with (c2:=(i0 ::= a0)). assumption. assumption.
          SSSSCase "c2_2 = ::=". simpl. apply CSeq_congruence.
            unfold constfold_0plus in *. assumption. assumption.
          SSSSCase "c2_2 = ;;". 



    
    assert (H: cequiv (c1;; c2) ((constfold_0plus c1);; (constfold_0plus c2))).
      apply CSeq_congruence. assumption. assumption.
    assert (H1: cequiv ((constfold_0plus c1);; (constfold_0plus c2)) (constfold_0plus (c1;; c2))). 
     destruct c1. unfold constfold_0plus. simpl.
        SCase "SKIP".
          assert (H1: cequiv (SKIP;; (constfold_0plus c2)) (SKIP;; c2)).
            apply CSeq_congruence. apply refl_cequiv. apply sym_cequiv. assumption.
          assert (H2: cequiv (SKIP;; c2) (optimize_0plus_com c2)).
            assert (H3: cequiv (SKIP;;c2) c2). 
              unfold cequiv. split. apply skip_left. apply skip_left.
            apply trans_cequiv with (c2:=c2). assumption. apply optimize_0plus_com_sound.
            unfold constfold_0plus in H1. apply trans_cequiv with (c2:=(SKIP;; c2)). assumption.
            assumption.
        SCase "::=". 
          
        assert (H1: cequiv (SKIP;; optimize_0plus_com (fold_constants_com c2)) c2).
          
    destruct c1.
      assert (H1: cequiv (SKIP;;c2) c2). 
      unfold cequiv. split. apply skip_left. apply skip_left.
      apply trans_cequiv with (c2:=c2). assumption. apply optimize_0plus_com_sound. 
      SCase "::=".
        destruct c2.
          SSCase "c2=SKIP".
          assert (H:cequiv (i::=a) (optimize_0plus_com (i::=a))).
          apply optimize_0plus_com_sound. 
          assert (H1: cequiv (i::=a;;SKIP) (i::=a)). 
          unfold cequiv. split. apply skip_right. apply skip_right. 
          apply trans_cequiv with (c2:=(i::=a)). assumption. assumption.
        SSCase "c2 = ::=".
          unfold constfold_0plus in IHc1. simpl in IHc1. 
          unfold constfold_0plus in IHc2. simpl in IHc2. simpl.
          apply CSeq_congruence. assumption. assumption.
        simpl.
      apply optimize_0plus_com_sound.
      assert (H:cequiv c2 (fold_constants_com c2)).
      apply fold_constants_com_sound. 
      assert (H1: cequiv (SKIP;;c2) c2). 
      unfold cequiv. split. apply skip_left. apply skip_left. 
      apply trans_cequiv with (c2:=c2). assumption. apply optimize_0plus_com_sound. 
    assert (H: cequiv ((constfold_0plus c1);;(constfold_0plus c2)) (constfold_0plus (c1;; c2))).
    unfold constfold_0plus. simpl.
    induction c1.  
    SCase "c1=SKIP". simpl.
      unfold constfold_0plus in IHc2.
      assert (H:cequiv c2 (fold_constants_com c2)).
      apply fold_constants_com_sound. 
      assert (H1: cequiv (SKIP;;c2) c2). 
      unfold cequiv. split. apply skip_left. apply skip_left. 
      apply trans_cequiv with (c2:=c2). assumption. apply optimize_0plus_com_sound. 
    assumption.
    



assert (H: cequiv ((constfold_0plus c1);;(constfold_0plus c2)) (constfold_0plus (c1;; c2))).
    
    split.
      SCase "->".
        intros. inversion H. subst. unfold constfold_0plus.
        destruct c1. simpl. unfold constfold_0plus in H5. simpl in H5. simpl.
    unfold constfold_0plus. 
    destruct c1.
    SCase "c1=SKIP". simpl.
      unfold constfold_0plus in IHc2.
      assert (H:cequiv c2 (fold_constants_com c2)).
      apply fold_constants_com_sound. 
      assert (H1: cequiv (SKIP;;c2) c2). 
      unfold cequiv. split. apply skip_left. apply skip_left. 
      apply trans_cequiv with (c2:=c2). assumption. assumption.
    SCase "c1 = ::=".
      simpl. destruct c2.
        SSCase "c2=SKIP".
          assert (H:cequiv (i::=a) (optimize_0plus_com (i::=a))).
          apply optimize_0plus_com_sound. 
          assert (H1: cequiv (i::=a;;SKIP) (i::=a)). 
          unfold cequiv. split. apply skip_right. apply skip_right. 
          apply trans_cequiv with (c2:=(i::=a)). assumption. assumption.
        SSCase "c2 = ::=".
          unfold constfold_0plus in IHc1. simpl in IHc1. 
          unfold constfold_0plus in IHc2. simpl in IHc2. simpl.
          apply CSeq_congruence. assumption. assumption.
        SSCase "c2 = ;;".
          destruct c2_1. 
          SSSCase "c2_1 = SKIP". 
            unfold constfold_0plus. simpl. 
            unfold constfold_0plus in IHc1. simpl in IHc1.
            unfold constfold_0plus in IHc2. simpl in IHc2. 
            apply CSeq_congruence. assumption. assumption.
          SSSCase "c2_1 = ::=".
          unfold constfold_0plus in IHc1. simpl in IHc1. 
          unfold constfold_0plus in IHc2. 
          unfold constfold_0plus. simpl.
          destruct c2_2.
            SSSSCase "c2_2 = SKIP". simpl.
              apply CSeq_congruence. assumption. assumption.
            SSSSCase "c2_2 = ::=".
              simpl. apply CSeq_congruence. assumption. assumption.
            SSSSCase "c2_2 = ;;". simpl.
            
    simpl.
destruct c2. simpl.
      unfold cequiv. split. intros. inversion H. subst. inversion H2. subst. assumption.  
      intros. apply E_Seq with (st':=st). apply E_Skip. assumption.
      assert (H:cequiv (i::=a) (optimize_0plus_com (i ::= a))).
      apply optimize_0plus_com_sound. 
      assert (H1: cequiv (SKIP;; i::= a) (i::=a)). 
      unfold cequiv. split. apply skip_left. apply skip_left. 
      apply trans_cequiv with (c2:= (i ::= a)). assumption. assumption.
      assert (H1: cequiv (SKIP;; c2_1;; c2_2) (c2_1;; c2_2)).
        unfold cequiv. split. apply skip_left. apply skip_left.
      apply trans_cequiv with (c2:= (c2_1;; c2_2)). assumption. 
      assert (H:cequiv (c2_1;; c2_2) (optimize_0plus_com (c2_1;; c2_2))). apply optimize_0plus_com_sound. assumption.
      simpl. unfold cequiv. split. intros.
      inversion H. subst. inversion H2. subst.
      assert (
      replace (optimize_0plus_aexp a) with a. assumption.
        apply 


unfold constfold_0plus in IHc1. simpl in IHc1. SKIP apply E_Seq in H.
      replace (SKIP;; SKIP) with SKIP. apply refl_cequiv.
        apply skip_left.
Qed.

