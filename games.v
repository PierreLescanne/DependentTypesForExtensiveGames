(* Time-stamp: "2017-01-28 11:37:23 libres" *)
(****************************************************************)
(*                           games.v                            *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.6                            January 2016  *)
(****************************************************************)
Section Games.
Require Import List.

(* Agents and Choices *)
Variable Agent : Set.
Variable Choice : Agent -> Set.

(* Utilities *)
Variable Utility: Agent -> Set.

(* preference on Utility *)
Require Import Relations.
Variable pref: forall a: Agent, relation (Utility a).

Hypothesis pref_is_preorder: forall a: Agent, preorder (Utility a) (pref a).

(* Strategy profiles *)
CoInductive StratProf  : Set :=
| sLeaf : (forall a:Agent, Utility a) -> StratProf
| sNode : forall (a:Agent),
            Choice a -> (Choice a -> StratProf) -> StratProf.

  Notation "<< f >>" := (sLeaf f).
  Notation "<< a , c , next >>" := (sNode a c next).

Definition StratProf_identity (s:StratProf): StratProf :=
match (s:StratProf) return StratProf with
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
| gLeaf :  (forall a:Agent, Utility a) -> Game 
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

(** - Equality of Games *)

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

(* Along P, means that the predicate P is fulfiled 
   along the path given by the choices *)
CoInductive Along 
(P:StratProf -> Prop) : StratProf -> Prop :=
| AlongLeaf : forall f, Along P (<<f>>)
| AlongNode : forall (a:Agent)(c:Choice a)
                      (next:Choice a->StratProf),
          P (<<a,c,next>>) ->  Along P (next c) ->
               Along P (<<a,c,next>>).

(* Utility assignment *)

Definition UAssignment (s:StratProf)(H:↓↓ s): forall a:Agent, Utility a.
  induction H; assumption.
Defined.

Definition UAssignment':  forall s : StratProf, convergent s ->  (forall a:Agent, Utility a) :=
fun (s : StratProf) (H : convergent s) =>
convergent_rec (fun (s0 : StratProf) (_ : convergent s0) => (forall a:Agent, Utility a))
  (fun f : (forall a:Agent, Utility a) => f)
  (fun (a : Agent) (c : Choice a) (next : Choice a -> StratProf)
     (_ : ↓↓ (next c)) (IHconvergent : (forall a:Agent, Utility a)) => IHconvergent) s H.

(* Utility assignment as a relation*)
Inductive Uassign : StratProf ->  (forall a:Agent, Utility a) -> Prop :=
| UassignLeaf: forall f, Uassign (<<f>>) f
| UassignNode: forall  (a:Agent)(c:Choice a)
                       (ua: forall a',Utility a')
                       (next:Choice a -> StratProf),
    Uassign (next c) ua  -> Uassign (<<a,c,next>>) ua.

Lemma Uassign_Uassignment:
  forall (s:StratProf) (H: ↓↓ s), Uassign s (UAssignment s H).
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

(* == Inversion of Uassign == *)
(* Chlipala's solution *)
Lemma UassignNode_inv': forall  (s:StratProf) (ua:forall a,Utility a),
    Uassign s ua
    -> match s with
       | << a', c, next >> => Uassign (next c) ua
       | _ => True
       end.
Proof.
  destruct 1; auto.
Qed.

Lemma UassignNode_inv: forall (a:Agent) (ua:forall a,Utility a)
                           (next:Choice a -> StratProf)
                           (c:Choice a),
                     Uassign (<<a,c,next>>) ua -> Uassign (next c) ua.
Proof.
  intros.
  apply UassignNode_inv' in H.
  assumption.
Qed.

(* Monin's solution *)
Definition pr_Uassign {s} {ua} (x: Uassign s ua) :=
  let diag s ua0 :=
     match s with
     | << f >> =>
         forall X: (forall a, Utility a) -> Prop, 
         X f -> X ua0 
     | << a' , c , next >> =>
         forall X: (forall a, Utility a) -> Prop, 
         (forall ua, Uassign (next c) ua -> X ua) -> X ua0 
    end in
  match x in Uassign s ua return diag s ua with
  | UassignLeaf f => fun X k => k
  | UassignNode a c ut next ua => fun X k => k ut ua
  end.

Lemma UassignNode_inv_Monin:
   forall (a':Agent) (ua:forall a, Utility a) (next:Choice a' -> StratProf) (c:Choice a'),
   Uassign (<<a',c,next>>) ua -> Uassign (next c) ua.
intros until c. intro H. apply (pr_Uassign H). trivial.
Qed.

Lemma UassignLeaf_inv:
   forall (f ua:forall a, Utility a), Uassign << f >> ua -> ua = f.
intros f ua H. apply (pr_Uassign H). trivial.
Qed.

Lemma UniquenessUassign:
  forall s ua va, Uassign s ua -> Uassign s va -> ua=va.
Proof.
  intros until va.
  intros UassignU UassignV.
  induction UassignV.
  intros; apply UassignLeaf_inv; auto.
  apply IHUassignV. apply UassignNode_inv_Monin. assumption.
  Qed.

Lemma ExistenceUassign:
  forall (s:StratProf),
    (↓ s) -> exists (ua: forall a, Utility a), Uassign s ua.
Proof.
  intros s ConvS.
  elim ConvS.  
  intro.
  exists f.
  apply UassignLeaf.
  intros a0 c next ConvNextS Exu.
  elim Exu.
  intro u.  exists u.
  apply UassignNode.
  assumption.
Qed.

(* Finite Game *)
     
Inductive Finite : Game -> Set :=
| finGLeaf: forall f, Finite <|f|>
| finGNode: forall (a:Agent)(c:Choice a)(next: Choice a -> Game),
             forall c':Choice a, Finite (next c') ->
             Finite <|a,next|>.


(* Finite Strategy Profile *)
     
Inductive FiniteStratProf : StratProf -> Set :=
| finSLeaf: forall f, FiniteStratProf <<f>>
| finSNode: forall (a:Agent)(c:Choice a)(next: Choice a -> StratProf),
             forall c':Choice a, FiniteStratProf (next c') ->
             FiniteStratProf <<a,c,next>>.

(* Finitely broad game *)

Definition FinitelyBroad (g:Game): Prop :=
  exists (l: list StratProf), forall (s:StratProf),
      game s == g <-> In s l.

(* Finite History Game *)
     
Inductive FiniteHistoryGame : Game -> Prop :=
| finHorGLeaf: forall f, FiniteHistoryGame <|f|>
| finHorGNode: forall (a:Agent)(next: Choice a -> Game),
             (forall c':Choice a, FiniteHistoryGame (next c')) ->
             FiniteHistoryGame <|a,next|>.

(* Finite Horizon Strategy Profile *)
     
Inductive FiniteHistoryStratProf : StratProf -> Prop :=
| finHorSLeaf: forall f, FiniteHistoryStratProf <<f>>
| finHorSNode: forall (a:Agent) (c:Choice a)
                      (next: Choice a -> StratProf),
             (forall c':Choice a, FiniteHistoryStratProf (next c')) ->
             FiniteHistoryStratProf <<a,c,next>>.

(* == Subgame Perfect Equilibrium == *)

CoInductive SPE : StratProf -> Prop :=
| SPELeaf : forall (f: forall a:Agent, Utility a), SPE <<f>>
| SPENode :  forall (a:Agent)
                    (c c':Choice a)
                    (next:Choice a->StratProf)
                    (u u':forall a':Agent, Utility a'),
               ⇓ <<a,c,next>> -> 
               Uassign (next c') u' ->  Uassign (next c) u ->
               (pref a (u' a) (u a)) -> SPE (next c') ->
             SPE <<a,c,next>>.
End Games.

Section Divergence.

(* Agents and Choices *)
Variable Agent : Set.
Variable Choice : Agent -> Set.

(* Utilities *)
Variable Utility: Agent -> Set.

Definition StPr := StratProf Agent Choice Utility. 

(* preference on Utility *)
Require Import Relations.
Variable pref: forall a: Agent, relation (Utility a).

Arguments game [Agent Choice Utility] s.
Arguments SPE [Agent Choice Utility] pref s.

Notation "<< f >>" := (sLeaf Agent Choice Utility f).
Notation "<< a , c , next >>" := (sNode Agent Choice Utility a c next).
Notation "g == g'" := (gEqual Agent Choice Utility g g') (at level 80).

CoInductive Divergent : StratProf Agent Choice Utility -> Prop :=
| divNode : forall (a:Agent)(c:Choice a)(next:Choice a->StPr), 
    Divergent (next c) -> Divergent (<<a,c,next>>).

CoInductive good : StratProf Agent Choice Utility -> Prop :=
| goodNode :forall (a:Agent)(c:Choice a)
                   (next next':Choice a -> StPr), 
              game (<<a,c,next>>) == game (<<a,c,next'>>) ->
              SPE pref (<<a,c,next'>>) -> 
              good(<<a,c,next>>).

Definition AlongGood := Along Agent Choice Utility good.

End Divergence.
