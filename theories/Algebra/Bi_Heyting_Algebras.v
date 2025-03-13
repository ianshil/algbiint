Require Import Arith.
Require Import Lia.

    Class biHalg :=
      {
        (* Elements of the algebera *)
        nodes : Type ;

        (* Operations on the algebra *)
        one : nodes ; (* Greatest element *)
        zero : nodes ; (* Lowest element *)
        meet : nodes -> nodes -> nodes ;
        join : nodes -> nodes -> nodes ;
        rpc : nodes -> nodes -> nodes ; (* Relative Pseudo Complement *)
        subtr : nodes -> nodes -> nodes ; (* Subtraction *)

        (* Property of one *)
        greatest a : meet a one = a ;
        (* Property of zero *)
        lowest a : join a zero = a ;
        (* Property of meet *)
        mcomm a b : meet a b = meet b a ;
        massoc a b c : meet a (meet b c) = meet (meet a b) c ;
        mabsorp a b : meet a (join a b) = a ;
        (* Property of join *)
        jcomm a b : join a b = join b a ;
        jassoc a b c : join a (join b c) = join (join a b) c ;
        jabsorp a b : join a (meet a b) = a ;
        (* Property of rpc *)
        residuation a b c : (a = meet a (rpc b c)) <-> (meet a b = meet (meet a b) c) ;
        (* Property of subtr *)
        dresiduation a b c : (subtr a b = meet (subtr a b) c) <-> (a = meet a (join b c))
      }.



Section biHalg_props.

Variable BH : biHalg.

Definition aleq a b : Prop := a = meet a b.

Notation "a << b" := (aleq a b) (at level 80).

Fact high_one a : a << one.
Proof.
unfold aleq. symmetry ; apply greatest.
Qed.

Fact ord_resid a b c : a << rpc b c <-> meet a b << c.
Proof.
unfold aleq ; split ; intro ; [ rewrite <- residuation | rewrite residuation ] ; auto.
Qed.

Fact ord_dresid a b c : subtr a b << c <-> a << join b c.
Proof.
unfold aleq ; split ; intro ; [ rewrite <- dresiduation | rewrite dresiduation ] ; auto.
Qed.

Fact meet_id a : meet a a = a.
Proof.
pose (mabsorp a zero). rewrite lowest in e ; auto.
Qed.

Fact join_id a : join a a = a.
Proof.
pose (jabsorp a one). rewrite greatest in e ; auto.
Qed.

Lemma meet_absorp0 a b : meet a (meet a b) = meet a b.
Proof.
rewrite massoc. rewrite meet_id ; auto.
Qed.

Lemma meet_absorp1 a b : meet b (meet a b) = meet a b.
Proof.
rewrite (mcomm a b). rewrite massoc. rewrite meet_id ; auto.
Qed.

Lemma meet_absorp2 a b : meet (meet a b) a = meet a b.
Proof.
rewrite (mcomm a b). rewrite <- massoc. rewrite meet_id ; auto.
Qed.

Lemma meet_absorp3 a b : meet (meet a b) b = meet a b.
Proof.
rewrite <- massoc. rewrite meet_id ; auto.
Qed.

(* Properties of aleq. *)

Lemma aleq_trans a b c : a << b -> b << c -> a << c.
Proof.
unfold aleq ; intros H H0. rewrite H.
rewrite <- massoc. rewrite <- H0 ; auto.
Qed.

Lemma aleq_refl a : a << a.
Proof.
unfold aleq. symmetry. apply meet_id.
Qed.

Lemma aleq_antisym a b : a << b -> b << a -> a = b.
Proof.
unfold aleq ; intros H H0. rewrite H, H0. rewrite meet_absorp1 ; auto.
Qed.

(* Universal properties of meet *)

Fact meet_elim1 a b : meet a b << a.
Proof.
unfold aleq. rewrite (mcomm (meet a b) a).
rewrite massoc. rewrite meet_id ; auto.
Qed.

Fact meet_elim2 a b : meet a b << b.
Proof.
unfold aleq. rewrite <- massoc.
rewrite meet_id ; auto.
Qed.

Lemma glb a b c : c << a -> c << b -> c << meet a b.
Proof.
unfold aleq ; intros H H0.
rewrite massoc. rewrite <- H. auto.
Qed.

Lemma meet_deep a b c d : a << c -> b << d -> meet a b << meet c d.
Proof.
intros H H0. apply glb.
- apply aleq_trans with a ; auto. apply meet_elim1.
- apply aleq_trans with b ; auto. apply meet_elim2.
Qed.

(* Universal properties of join *)

Fact join_inj1 a b : a << join a b.
Proof.
unfold aleq. symmetry ; apply mabsorp.
Qed.

Fact join_inj2 a b : b << join a b.
Proof.
unfold aleq. symmetry. rewrite jcomm. apply mabsorp.
Qed.

Lemma eq_repres_aleq a b : a << b <-> b = join a b.
Proof.
split ; intro.
- unfold aleq in H.
  assert (join a b = join (meet a b) b). f_equal ; auto. rewrite H0.
  symmetry. rewrite jcomm, mcomm ; apply jabsorp.
- unfold aleq.
  assert (meet a b = meet a (join a b)). f_equal ; auto. rewrite H0.
  symmetry. apply mabsorp.
Qed.

Lemma lub a b c : a << c -> b << c -> join a b << c.
Proof.
repeat rewrite eq_repres_aleq ; intros.
rewrite <- jassoc. rewrite <- H0. auto.
Qed.

Lemma join_deep a b c d : a << c -> b << d -> join a b << join c d.
Proof.
intros H H0. apply lub.
- apply aleq_trans with c ; auto. apply join_inj1.
- apply aleq_trans with d ; auto. apply join_inj2.
Qed.

(* Distributivity *)

Lemma distr_meet_join a b c : meet a (join b c) = join (meet a b) (meet a c).
Proof.
apply aleq_antisym.
- rewrite mcomm. apply ord_resid. apply lub.
  + rewrite ord_resid. rewrite mcomm. apply join_inj1.
  + rewrite ord_resid. rewrite mcomm. apply join_inj2.
- apply lub.
  + apply meet_deep.
    * apply aleq_refl.
    * apply join_inj1.
  + apply meet_deep.
    * apply aleq_refl.
    * apply join_inj2.
Qed.

Lemma distr_join_meet a b c : join a (meet b c) = meet (join a b) (join a c).
Proof.
apply aleq_antisym.
- apply lub.
  + apply glb ; apply join_inj1.
  + apply meet_deep ; apply join_inj2.
- apply ord_resid. apply lub ; rewrite ord_resid.
  + rewrite mcomm. apply ord_resid. apply lub.
    * apply ord_resid. rewrite meet_id. apply join_inj1.
    * apply ord_resid. apply aleq_trans with a.
      -- apply meet_elim2.
      -- apply join_inj1.
  + rewrite mcomm. apply ord_resid. apply lub.
    * apply ord_resid. apply aleq_trans with a.
      -- apply meet_elim1.
      -- apply join_inj1.
    * apply ord_resid. rewrite mcomm. apply join_inj2.
Qed.

(* Properties of rpc. *)

Lemma mp a b : meet a (rpc a b) << b.
Proof.
pose (meet_elim2 a (rpc a b)). rewrite ord_resid in a0.
rewrite mcomm in a0. rewrite meet_absorp0 in a0 ; auto.
Qed.

(* Properties of subtr. *)

Lemma bi_LEM a : one = join a (subtr one a).
Proof.
apply aleq_antisym.
- rewrite <- ord_dresid. apply aleq_refl.
- unfold aleq. symmetry ; apply greatest.
Qed.

Lemma subtr_meet a b : subtr a b << meet a (subtr one b).
Proof.
rewrite ord_dresid. rewrite distr_join_meet. rewrite <- bi_LEM.
rewrite greatest. apply join_inj2.
Qed.

Lemma double_coneg a : subtr one (subtr one a) << a.
Proof.
repeat rewrite ord_dresid. rewrite jcomm. rewrite <- ord_dresid. apply aleq_refl.
Qed.

(* Property of zero *)

Fact low_zero a : zero << a.
Proof.
apply eq_repres_aleq. symmetry.
rewrite jcomm. apply lowest.
Qed.

(* Axioms *)

Lemma alg_A1 a b : one << rpc a (rpc b a).
Proof.
repeat rewrite ord_resid. rewrite (mcomm one a). rewrite greatest.
apply meet_elim1.
Qed.

Lemma alg_A2 a b c : one << rpc (rpc a (rpc b c)) (rpc (rpc a b) (rpc a c)).
Proof.
repeat rewrite ord_resid. rewrite (mcomm one (rpc a (rpc b c))). rewrite greatest.
rewrite mcomm.
apply aleq_trans with (meet a (meet (rpc b c) (rpc a b))).
- repeat rewrite massoc. apply meet_deep.
  + apply glb.
    * apply meet_elim1.
    * apply mp.
  + apply aleq_refl.
- rewrite (mcomm (rpc b c) _). apply aleq_trans with (meet a (meet b (rpc b c))).
  + apply glb.
    * apply meet_elim1.
    * rewrite massoc. apply meet_deep.
      -- apply mp.
      -- apply aleq_refl.
  + apply aleq_trans with (meet b (rpc b c)).
    * apply meet_elim2.
    * apply mp.
Qed.

Lemma alg_A3 a b : one << rpc a (join a b).
Proof.
rewrite ord_resid. rewrite mcomm ; rewrite greatest. apply join_inj1.
Qed.

Lemma alg_A4 a b : one << rpc b (join a b).
Proof.
rewrite ord_resid. rewrite mcomm ; rewrite greatest. apply join_inj2.
Qed.

Lemma alg_A5 a b c : one << rpc (rpc a c) (rpc (rpc b c) (rpc (join a b) c)).
Proof.
repeat rewrite ord_resid. rewrite (mcomm one _). rewrite greatest.
rewrite mcomm. repeat rewrite <- ord_resid.
apply lub ; rewrite ord_resid.
- apply aleq_trans with (meet a (rpc a c)).
  + repeat rewrite massoc. apply meet_elim1.
  + apply mp.
- rewrite (mcomm (rpc a c) _). apply aleq_trans with (meet b (rpc b c)).
  + repeat rewrite massoc. apply meet_elim1.
  + apply mp.
Qed.

Lemma alg_A6 a b : one << rpc (meet a b) a.
Proof.
rewrite ord_resid. rewrite mcomm ; rewrite greatest. apply meet_elim1.
Qed.

Lemma alg_A7 a b : one << rpc (meet a b) b.
Proof.
rewrite ord_resid. rewrite mcomm ; rewrite greatest. apply meet_elim2.
Qed.

Lemma alg_A8 a b c : one << rpc (rpc c a) (rpc (rpc c b) (rpc c (meet a b))).
Proof.
repeat rewrite ord_resid. rewrite (mcomm one _). rewrite greatest.
rewrite mcomm. apply glb.
- apply aleq_trans with (meet c (rpc c a)).
  + repeat rewrite massoc. apply meet_elim1.
  + apply mp.
- rewrite (mcomm (rpc c a) _). apply aleq_trans with (meet c (rpc c b)).
  + repeat rewrite massoc. apply meet_elim1.
  + apply mp.
Qed.

Lemma alg_A9 a : one << rpc zero a.
Proof.
rewrite ord_resid. rewrite eq_repres_aleq.
rewrite mcomm ; rewrite greatest. rewrite jcomm. symmetry ; apply lowest.
Qed.

Lemma alg_A10 a : one << rpc a one.
Proof.
rewrite ord_resid. unfold aleq. symmetry ; apply greatest.
Qed.

Lemma alg_BA1 a b : one << rpc a (join b (subtr a b)).
Proof.
rewrite ord_resid. rewrite mcomm ; rewrite greatest.
rewrite <- ord_dresid. apply aleq_refl.
Qed.

Lemma alg_BA2 a b : one << rpc (subtr a b) (subtr one (rpc a b)).
Proof.
rewrite ord_resid. rewrite mcomm ; rewrite greatest.
rewrite ord_dresid. rewrite jcomm. apply ord_dresid.
apply aleq_trans with (meet a (rpc a b)).
- apply aleq_trans with (meet a (subtr one (subtr one (rpc a b)))).
  + apply subtr_meet.
  + apply meet_deep.
    * apply aleq_refl.
    * apply double_coneg.
- apply mp.
Qed.

Lemma alg_BA3 a b c : one << rpc (subtr (subtr a b) c) (subtr a (join b c)).
Proof.
rewrite ord_resid. rewrite mcomm ; rewrite greatest.
repeat rewrite ord_dresid. rewrite jassoc.
apply ord_dresid. apply aleq_refl.
Qed.

Lemma alg_BA4 a b : one << rpc (rpc (subtr a b) zero) (rpc a b).
Proof.
repeat rewrite ord_resid. rewrite (mcomm one _) ; rewrite greatest.
rewrite mcomm. apply ord_resid.
apply aleq_trans with (join (rpc (rpc (subtr a b) zero) zero) b).
- apply aleq_trans with (join (subtr a b) b).
  + rewrite jcomm. apply ord_dresid. apply aleq_refl.
  + apply join_deep.
    * rewrite ord_resid. apply mp.
    * apply aleq_refl.
- apply lub.
  + apply ord_resid. apply aleq_trans with zero.
    * rewrite mcomm ; apply mp.
    * apply eq_repres_aleq. symmetry. rewrite jcomm. apply lowest.
  + rewrite ord_resid. apply meet_elim1.
Qed.


(* Additional operators and properties. *)

Fixpoint DN_alg n a : nodes :=
  match n with
  | 0 => a
  | S n => rpc (subtr one (DN_alg n a)) zero
  end.

Fixpoint list_meet l : nodes :=
  match l with
  | nil => one
  | cons a l => meet a (list_meet l)
  end.

Lemma list_meet_all l : forall a, List.In a l -> aleq (list_meet l) a.
Proof.
induction l ; intros ; cbn ; try contradiction.
inversion H ; subst ; auto.
- apply meet_elim1.
- eapply aleq_trans.
  + apply meet_elim2.
  + apply IHl ; auto.
Qed.

End biHalg_props.