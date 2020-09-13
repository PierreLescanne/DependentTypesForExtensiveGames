(* Time-stamp: "2018-02-08 18:30:35 pierre" *)
(****************************************************************)
(*                multistage_games.v                            *)
(*                                                              *)
(*           © Pierre Lescanne  (June 2016)                     *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.6              January 2016 -- March 2017  *)
(****************************************************************)
Section MultiStageGames.
Require Import List games_Ut_Ch_Dependent.

Variables (Agent: Set) (Choice Utility: Agent -> Set).

CoInductive MGame :=
| mgLeaf: (forall a: Agent, Utility a) -> MGame
| mgNode: ((forall a: Agent, Choice a) -> MGame) -> MGame.
Notation "<! f !>" := (mgLeaf f).
Notation "<? next !>" := (mgNode next).

(** - Equality of Games *)

CoInductive mgEqual: MGame -> MGame -> Prop :=
  | eq_gLeaf: forall f, mgEqual <! f !> <! f !>
  | eq_gNode: forall (next next':(forall a, Choice a) -> MGame),
                     (forall (c:forall a:Agent,Choice a), mgEqual (next c) (next' c)) ->
                      mgEqual <?next!> <?next'!>.

  Notation "g == g'" := (mgEqual g g') (at level 80).

Definition MGame_identity (g:MGame): MGame :=
  match g with
    | <!f!> =>  <!f!>
    | <?next!> => <?next!>
  end.

Lemma MGame_decomposition :
  forall g:MGame, MGame_identity g = g.
Proof.
 destruct g; reflexivity.
Qed.

  (** - Reflexivity of the equality *)
Lemma refMGEqual: forall g, g == g.
Proof.
 cofix refMGEqual;
  destruct g;
  [apply eq_gLeaf
  | apply eq_gNode; intro;  apply refMGEqual].
Qed.

(** Strategy profile *)
CoInductive MSStratProf :=
| mssLeaf:  (forall a: Agent, Utility a) -> MSStratProf
| mssNode: (forall a: Agent, Choice a) ->
           ((forall a: Agent, Choice a) -> MSStratProf) ->
           MSStratProf.
  Notation "<< f >>" := (mssLeaf f).
  Notation "<< c , next >>" := (mssNode c next).

Definition mgame: MSStratProf -> MGame.
  cofix game.
  intro s; case s;
  [intro f; exact (<!f!>)
  | intros c next; apply mgNode;
    auto;
    intro c';
    apply game;
    apply next;
    apply c].
Defined.

(** - Convergence of Strategy Profiles *)

Inductive Convergent: MSStratProf -> Prop :=
| ConvLeaf: forall f, Convergent <<f>>
| ConvNode: forall (choices: (forall a: Agent, Choice a) -> Prop)
                   (c: forall a:Agent, Choice a)
                   (next: (forall a: Agent, Choice a) -> MSStratProf),
              Convergent (next c) -> Convergent <<c,next>>.
    Notation "↓ s " := (Convergent s) (at level 5).

(** - Finitely broad game *)

Definition FinitelyBroad (g:MGame): Prop :=
  exists (l: list MSStratProf), forall (s:MSStratProf),
      mgame s == g <-> In s l.
    
(** - Utility assignment as a relation *)
Inductive Uassign: MSStratProf ->  (forall a:Agent, Utility a) -> Prop :=
| UassignLeaf: forall f, Uassign (<<f>>) f
| UassignNode: forall (c: forall a:Agent, Choice a)
                      (ua: forall a: Agent, Utility a)
                      (next:(forall a:Agent, Choice a) -> MSStratProf),
                 Uassign (next c) ua  -> Uassign (<<c,next>>) ua.

Definition pr_Uassign {s} {ua} (x: Uassign s ua) :=
  let diag s u0 :=
     match s with
     | << f >> =>
         forall X: (forall a:Agent, Utility a) -> Prop, 
           X f -> X u0 
     | <<c,next>> =>
         forall X: (forall a:Agent, Utility a) -> Prop, 
           (forall ua, Uassign (next c) ua -> X ua) -> X u0
    end in
  match x in Uassign s ua return diag s ua with
  | UassignLeaf f => fun X k => k
  | UassignNode c ut next ua => fun X k => k ut ua
  end.

Lemma UassignNode_inv:
  forall (ua: forall a:Agent, Utility a)
         (c:forall a:Agent, Choice a)
         (next:(forall a:Agent,Choice a) -> MSStratProf),
   Uassign (<<c,next>>) ua -> Uassign (next c) ua.
intros until c. intros next H. apply (pr_Uassign H). trivial.
Qed.

Lemma UassignLeaf_inv:
   forall f (ua: forall a:Agent, Utility a), Uassign << f >> ua -> ua = f.
intros f ua H; apply (pr_Uassign H); trivial.
Qed.

Lemma UniquenessUassign:
  forall s ua ua', Uassign s ua -> Uassign s ua' -> ua=ua'.
Proof.
  intros until ua';
  intros UassignU UassignU';
  induction UassignU';
  [apply UassignLeaf_inv; auto
  | apply IHUassignU'; apply UassignNode_inv;
    assumption].
Qed.

Lemma ExistenceUassign:
  forall (s:MSStratProf),
    (↓ s) -> exists (ua: forall a:Agent, Utility a), Uassign s ua.
Proof.
    intros s ConvS; elim ConvS;
    [intro;  exists f; apply UassignLeaf
    | intros choices c next ConvNextS Exua;
      elim Exua; intros u H;
      exists u; apply UassignNode; assumption].
Qed.

End MultiStageGames.
