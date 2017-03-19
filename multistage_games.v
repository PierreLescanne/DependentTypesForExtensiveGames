(* Time-stamp: "2017-03-19 17:13:50 pierre" *)
(****************************************************************)
(*                           games.v                            *)
(*                                                              *)
(**          © Pierre Lescanne  (June 2016)                     *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.6              January 2016 -- March 2017  *)
(****************************************************************)
Section MultiStageGames.
Require Import List games.

Variables (Agent: Set) (Choice Utility: Agent -> Set).

CoInductive MSGame :=
| msgLeaf: (forall a: Agent, Utility a) -> MSGame
| msgNode: ((forall a: Agent, Choice a) -> Prop) -> ((forall a: Agent, Choice a) -> MSGame)
           -> MSGame.
Notation "<! f !>" := (msgLeaf f).
Notation "<! choices , next !>" := (msgNode choices next).

(** - Equality of Games *)

CoInductive msgEqual: MSGame -> MSGame -> Prop :=
  | eq_gLeaf: forall f, msgEqual <! f !> <! f !>
  | eq_gNode: forall (choices choices':(forall a, Choice a) -> Prop)
                     (next next':(forall a, Choice a) -> MSGame),
                     (forall (c:forall a: Agent, Choice a), (choices c <-> choices' c)) ->
                     (forall (c:forall a:Agent,Choice a), msgEqual (next c) (next' c)) ->
                     msgEqual <!choices,next!> <!choices,next'!>.

  Notation "g == g'" := (msgEqual g g') (at level 80).

  (* reflexivity of the equality *)
Lemma refMSGEqual: forall g, g == g.
Proof.
  cofix;
  destruct g;
  [apply eq_gLeaf
  | apply eq_gNode with (choices:=P)(choices':=P);
      [intros; split; [intro; auto | intro; auto]
      | intros; apply refMSGEqual]].
Qed.

(* Strategy profile *)
CoInductive MSStratProf :=
| mssLeaf:  (forall a: Agent, Utility a) -> MSStratProf
| mssNode: ((forall a: Agent, Choice a) -> Prop) ->
           (forall a: Agent, Choice a) ->
           ((forall a: Agent, Choice a) -> MSStratProf) ->
           MSStratProf.
  Notation "<< f >>" := (mssLeaf f).
  Notation "<< choices , c , next >>" := (mssNode choices c next).

Definition msgame: MSStratProf -> MSGame.
  cofix.
  intro s; case s;
  [intro f; exact (<!f!>)
  | intros choices c next; apply msgNode;
    auto;
    intro c';
    apply game;
    apply next;
    apply c].
Defined.

(* Convergence of Strategy Profiles *)

Inductive Convergent: MSStratProf -> Prop :=
| ConvLeaf: forall f, Convergent <<f>>
| ConvNode: forall (choices: (forall a: Agent, Choice a) -> Prop)
                   (c: forall a:Agent, Choice a)
                   (next: (forall a: Agent, Choice a) -> MSStratProf),
             Convergent (next c) -> Convergent <<choices,c,next>>.
    Notation "↓ s " := (Convergent s) (at level 5).

(* Finitely broad game *)

Definition FinitelyBroad (g:MSGame): Prop :=
  exists (l: list MSStratProf), forall (s:MSStratProf),
      msgame s == g <-> In s l.
    
(* Utility assignment as a relation *)
Inductive Uassign: MSStratProf ->  (forall a:Agent, Utility a) -> Prop :=
| UassignLeaf: forall f, Uassign (<<f>>) f
| UassignNode: forall  (choices: (forall a: Agent, Choice a) -> Prop)
                       (c: forall a:Agent, Choice a)
                       (ua: forall a: Agent, Utility a)
                       (next:(forall a:Agent, Choice a) -> MSStratProf),
    Uassign (next c) ua  -> Uassign (<<choices,c,next>>) ua.

Definition pr_Uassign {s} {ua} (x: Uassign s ua) :=
  let diag s u0 :=
     match s with
     | << f >> =>
         forall X: (forall a:Agent, Utility a) -> Prop, 
           X f -> X u0 
     | <<choices,c,next>> =>
         forall X: (forall a:Agent, Utility a) -> Prop, 
           (forall ua, Uassign (next c) ua -> X ua) -> X u0
    end in
  match x in Uassign s ua return diag s ua with
  | UassignLeaf f => fun X k => k
  | UassignNode choices c ut next ua => fun X k => k ut ua
  end.

Lemma UassignNode_inv:
  forall (ua: forall a:Agent, Utility a)
         (choices: (forall a: Agent, Choice a) -> Prop)
         (c:forall a:Agent, Choice a)
         (next:(forall a:Agent,Choice a) -> MSStratProf),
   Uassign (<<choices, c,next>>) ua -> Uassign (next c) ua.
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
  | apply IHUassignU'; apply UassignNode_inv with (choices:=choices);
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
