(* Time-stamp: "2016-09-05 17:28:02 pierre" *)
(****************************************************************)
(*                           games.v                            *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.4pl4                January -- April 2016  *)
(****************************************************************)
Section Games.
Require Import List.

(* Agents Utilities and Choices *)
Variables (Agent Utility: Set) (Choice: Agent -> Set).

(* preference on Utility *)
Require Import Relations.
Variable preference: relation Utility.

Hypothesis preference_is_preorder: preorder Utility preference.
    Infix "=<" := preference (at level 100).

(* Strategy profiles *)
CoInductive StratProf  : Set :=
| sLeaf : (Agent -> Utility) -> StratProf
| sNode : forall (a:Agent), Choice a -> (Choice a -> StratProf) -> StratProf.
  Notation "<< f >>" := (sLeaf f).
  Notation "<< a , c , next >>" := (sNode a c next).

Definition StratProf_identity (s:StratProf): StratProf :=
match s with
| <<f>> =>  <<f>>
| <<a,c,next>> => <<a,c,next>>
end.

Lemma StratProf_decomposition :
  forall s:StratProf, StratProf_identity s = s.
Proof.
 destruct s; reflexivity.
Qed.

(* Games *)
CoInductive Game : Set :=
| gLeaf : (Agent -> Utility) -> Game 
| gNode : forall (a:Agent), (Choice a -> Game) -> Game.
  Notation "<| f |>" := (gLeaf f).
  Notation "<| a , next |>" := (gNode a next).

Definition Game_identity (g:Game): Game :=
match g with
| <|f|> =>  <|f|>
| <|a,next|> => <|a,next|>
end.

Lemma Game_decomposition :
  forall g:Game, Game_identity g = g.
Proof.
 destruct g; reflexivity.
Qed.

(* Equality of games *)
CoInductive gEqual: Game -> Game -> Prop :=
| gEqualLeaf: forall f, gEqual (<| f |>) (<| f |>)
| gEqualNode: forall (a:Agent)(next next':Choice a->Game),
  (forall (c:Choice a), gEqual (next c) (next' c)) ->  
  gEqual (<|a,next|>) (<|a,next'|>).

Lemma refGEqual: forall g, gEqual g g.
Proof.
  cofix refGEqual.
  destruct g.  
  apply gEqualLeaf.
  apply gEqualNode.
  intros.
  apply refGEqual.
Qed.

Notation "g == g'" := (gEqual g g') (at level 80).

(* The game of a strategy profile *)
Definition game : StratProf -> Game :=
cofix game_co (s : StratProf) : Game :=
  match s with
  | << f >> => <| f |>
  | << a, _, next >> => <| a, fun c : Choice a => game_co (next c) |>
  end.

Lemma gameLeaf: forall f, game <<f>> = <|f|>.
Proof.
  intro.
  rewrite <- Game_decomposition with (g:= game <<f>>).
  simpl.
  reflexivity.
Qed.

Lemma gameNode: forall a c next, game <<a,c,next>> = <|a,fun c => game(next c)|>.
Proof.
  intros.
  rewrite <- Game_decomposition with (g:= game <<a,c,next>>).
  simpl.
  reflexivity.
Qed.

(* Finitely broad game *)

Definition FinitelyBroad (g:Game): Prop :=
  exists (l: list StratProf), forall (s:StratProf),
      game s == g <-> In s l.

(* Finite Horizon Game *)
     
Inductive FiniteHistoryGame : Game -> Prop :=
| finHorGLeaf: forall f, FiniteHistoryGame <|f|>
| finHorGNode: forall (a:Agent)(next: Choice a -> Game),
             (forall c':Choice a, FiniteHistoryGame (next c')) ->
             FiniteHistoryGame <|a,next|>.

(* Convergent Strategy Profile *)

Inductive Convergent: StratProf -> Prop :=
| ConvLeaf: forall f, Convergent <<f>>
| ConvNode: forall (a:Agent) (c:Choice a)(next: Choice a -> StratProf),
             Convergent (next c) ->
             Convergent <<a,c,next>>.
    Notation "↓ s " := (Convergent s) (at level 5).

Inductive convergent : StratProf -> Set :=
| convLeaf: forall f, convergent <<f>>
| convNode: forall (a:Agent)(c:Choice a)(next: Choice a -> StratProf),
             convergent (next c) ->
             convergent <<a,c,next>>.
     Notation "↓↓ s " := (convergent s) (at level 5).

(* Finite Strategy Profile *)
     
Inductive finiteStratProf : StratProf -> Set :=
| finSLeaf: forall f, finiteStratProf <<f>>
| finSNode: forall (a:Agent)(c:Choice a)(next: Choice a -> StratProf),
             forall c':Choice a, finiteStratProf (next c') ->
             finiteStratProf <<a,c,next>>.

(* Always *)

CoInductive Always (P:StratProf -> Prop) : StratProf -> Prop :=
| AlwaysLeaf : forall f, Always P (<<f>>)
| AlwaysNode : forall (a:Agent)(c:Choice a)
                      (next:Choice a->StratProf),
          P (<<a,c,next>>) ->  (forall c', Always P (next c')) ->
               Always P (<<a,c,next>>).
    Notation "□ P" := (Always P) (at level 30).

Definition AlwaysConvergent := □ (fun s:StratProf => (↓ (s))).
Notation "⇓ s" := (AlwaysConvergent s)
                    (at level 15).

(* Utility assignment *)

Definition UAssignment (s:StratProf)(H:↓↓ s):Agent -> Utility.
  induction H; assumption.
Defined.

Definition UAssignment':  forall s : StratProf, convergent s -> Agent -> Utility :=
fun (s : StratProf) (H : convergent s) =>
convergent_rec (fun (s0 : StratProf) (_ : convergent s0) => Agent -> Utility)
  (fun f : Agent -> Utility => f)
  (fun (a : Agent) (c : Choice a) (next : Choice a -> StratProf)
     (_ : ↓↓ (next c)) (IHconvergent : Agent -> Utility) => IHconvergent) s H.

(* Utility assignment as a relation*)
Inductive Uassign : StratProf -> Agent -> Utility -> Prop :=
| UassignLeaf: forall a f, Uassign (<<f>>) a (f a)
| UassignNode: forall  (a a':Agent)(c:Choice a')
                       (u:Utility)
                       (next:Choice a' -> StratProf),
    Uassign (next c) a u  -> Uassign (<<a',c,next>>) a u.

Lemma Uassign_Uassignment:
  forall (s:StratProf) (a:Agent) (H: ↓↓ s),
                  Uassign s a (UAssignment s H a).
Proof.
  intros.
  elim H.
  simpl.
  apply UassignLeaf.
  intros.
  simpl.
  apply UassignNode.
  assumption.
Qed.

(* Monin's solution *)
Definition pr_Uassign {s} {a} {u} (x: Uassign s a u) :=
  let diag s a0 u0 :=
     match s with
     | << f >> =>
         forall X: Agent -> Utility -> Prop, 
         (forall a, X a (f a)) -> X a0 u0 
     | << a' , c , next >> =>
         forall X: Agent -> Utility -> Prop, 
         (forall a u, Uassign (next c) a u -> X a u) -> X a0 u0 
    end in
  match x in Uassign s a u return diag s a u with
  | UassignLeaf a f => fun X k => k a
  | UassignNode a a' c ut next ua => fun X k => k a ut ua
  end.

Lemma UassignNode_inv_Monin:
   forall (a a':Agent) (u:Utility) (next:Choice a' -> StratProf) (c:Choice a'),
   Uassign (<<a',c,next>>) a u -> Uassign (next c) a u.
intros until c. intro ua. apply (pr_Uassign ua). trivial.
Qed.

Lemma UassignLeaf_inv:
   forall (a:Agent) f (u:Utility), Uassign << f >> a u -> u = f a.
intros a f u ua. apply (pr_Uassign ua). trivial.
Qed.

Lemma UniquenessUassign:
  forall s a u v, Uassign s a u -> Uassign s a v -> u=v.
Proof.
  intros until v.
  intros UassignU UassignV.
  induction UassignV.
  intros; apply UassignLeaf_inv; auto.
  apply IHUassignV. apply UassignNode_inv_Monin. assumption.
  Qed.

Lemma ExistenceUassign:
  forall (s:StratProf)(a:Agent),
    (↓ s) -> exists (u:Utility), Uassign s a u.
Proof.
  intros s a ConvS.
  elim ConvS.  
  intro.
  exists (f a).
  apply UassignLeaf.
  intros a0 c next ConvNextS Exu.
  elim Exu.
  intro u.  exists u.
  apply UassignNode.
  assumption.
Qed.

(* == Subgame Perfect Equilibrium == *)

CoInductive SPE : StratProf -> Prop :=
| SPELeaf : forall (f:Agent->Utility), SPE <<f>>
| SPENode :  forall (a:Agent)
                    (c c':Choice a)
                    (next:Choice a->StratProf)
                    (u u':Utility),
               ⇓ <<a,c,next>> -> 
               Uassign (next c') a u' ->  Uassign (next c) a u ->
               (u' =< u) -> SPE (next c') ->
             SPE <<a,c,next>>.

End Games.

(* ===================================== *)

Section Divergence.

(* Agents Utilities and Choices *)
Variables (Agent Utility: Set) (Choice: Agent -> Set).

Definition StPr := StratProf Agent Utility Choice. 

(* preference on Utility *)
Require Import Relations.
Variable preference: relation Utility.

Arguments game [Agent Utility Choice] s.
Arguments SPE [Agent Utility Choice] preference s.

Notation "<< f >>" := (sLeaf Agent Utility Choice f).
Notation "<< a , c , next >>" := (sNode Agent Utility Choice a c next).
Notation "g == g'" := (gEqual Agent Utility Choice g g') (at level 80).

CoInductive Divergent : StratProf Agent Utility Choice -> Prop :=
| divNode : forall (a:Agent)(c:Choice a)(next:Choice a->StPr), 
    Divergent (next c) -> Divergent (<<a,c,next>>).

CoInductive good : StratProf Agent Utility Choice -> Prop :=
| goodNode :forall (a:Agent)(c:Choice a)
                   (next next':Choice a -> StPr), 
              (game (<<a,c,next>>) == game (<<a,c,next'>>) /\ 
              SPE preference (<<a,c,next'>>)) -> 
              good(<<a,c,next>>).

Definition AlwaysGood := Always Agent Utility Choice good.

End Divergence.
