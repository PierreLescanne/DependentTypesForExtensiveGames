(* Time-stamp: "2017-01-26 17:54:39 pierre" *)
(****************************************************************)
(*                       yingYang.v                             *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.6          January 2016  -- January 2017   *)
(****************************************************************)
Section YingYang.

Add LoadPath ".". 

Require Import games.
Require Import Relations.

(* Setting sets for agents and choices *)
Inductive AliceBob : Set := | Alice | Bob.
Inductive DorR : Set := | down | right.
Inductive YingYang: Set := | ying | yang.
Definition ChoiceYY: AliceBob -> Set := fun a => DorR.
Definition UtilityYY: AliceBob -> Set := fun a => YingYang.
Definition eqYY: forall a: AliceBob, relation (UtilityYY a) :=
  fun a :AliceBob => fun x:UtilityYY a => fun y:UtilityYY a => x=y.

Arguments StratProf [Agent Choice Utility].
Arguments Game [Agent Choice Utility].
Arguments UAssignment [Agent Choice Utility] s H a.
Arguments game [Agent Choice Utility] s.
Arguments Convergent [Agent Choice Utility] s.
Arguments AlwaysConvergent [Agent Choice Utility] s.
Arguments convLeaf [Agent Choice Utility] f.
Arguments convNode [Agent Choice Utility] a c next _.
Arguments SPE [Agent Choice Utility] pref  s.
Arguments Uassign [Agent Choice Utility] s u.
Arguments good [Agent Choice Utility] pref s.
Arguments gEqual [Agent Choice Utility] g1 g2.
Arguments Divergent  [Agent Choice Utility] s.
Arguments AlongGood  [Agent Choice Utility] pref s.

Notation "<< f >>" := (sLeaf AliceBob ChoiceYY UtilityYY f).
Notation "<< a , c , next >>" := 
  (sNode AliceBob ChoiceYY UtilityYY a c next).
Notation "[ x , y ]" := 
  (fun a:AliceBob => match a as AliceBob return (UtilityYY a) with Alice => x | Bob => y end).
Notation "<| f |>" := (gLeaf  AliceBob ChoiceYY UtilityYY f).
Notation "<| a , next |>" := (gNode AliceBob ChoiceYY UtilityYY a next).

Notation "s1 +++ s2" := 
  (fun c:DorR => match c with down => s1 | right => s2 end) 
  (at level 30).
Notation "↓ s " := (Convergent s) (at level 5).
Notation "⇓ s" := (AlwaysConvergent s)
                    (at level 15).
Notation "↑ s " := (Divergent s) (at level 5).
Notation "g == g'" := (gEqual g g') (at level 80).

Ltac decomp := rewrite <- StratProf_decomposition; simpl.

(* --------------------------------- *)
(**    Infinite Game Zero One        *)
(* --------------------------------- *)

(* Definitions *)
CoFixpoint yingYangAcBs := <<Alice, right, <<[yang,ying]>> +++ yingYangBsAc>>
  with yingYangBsAc := <<Bob, down, <<[ying,yang]>> +++ yingYangAcBs>>.

CoFixpoint yingYangAsBc := <<Alice, down, <<[yang,ying]>> +++ yingYangBcAs>>
  with yingYangBcAs := <<Bob, right, <<[ying,yang]>> +++ yingYangAsBc>>.

CoFixpoint yingYangAcBc := <<Alice, right, <<[yang,ying]>> +++ yingYangBcAc>>
  with yingYangBcAc := <<Bob, right, <<[ying,yang]>> +++ yingYangAcBc>>.

(* == Lemmas on utility assignments == *)

(* A continue Bob stops *)

Lemma UassignYyBsAc: Uassign yingYangBsAc [ying,yang].
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangBsAc); simpl.
  apply UassignNode.
  apply UassignLeaf.
Qed.

Lemma UassignYyAcBs: Uassign yingYangAcBs [ying,yang].
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangAcBs); simpl.
  apply UassignNode.
  apply UassignYyBsAc.
Qed.

(* A stops Bob continues *)
Lemma UassignYyAsBc: Uassign yingYangAsBc [yang,ying].
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangAsBc); simpl.
  apply UassignNode.
  apply UassignLeaf.
Qed.

Lemma UassignYyBcAs: Uassign yingYangBcAs [yang,ying].
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangBcAs); simpl.
  apply UassignNode.
  apply UassignYyAsBc.
Qed.

(* Lemmas on Convergence of strategy profiles *)
Lemma ConvYyBsAc: ↓ yingYangBsAc.
Proof.
  decomp.
  apply ConvNode.
  apply ConvLeaf.
Qed.

Lemma ConvYyAcBs: ↓ yingYangAcBs.
Proof.
  decomp.
  decomp.
  apply ConvNode.
  apply ConvYyBsAc.
Qed.

Lemma ConvYyAsBc: ↓ yingYangAsBc.
Proof.
  decomp;apply ConvNode; apply ConvLeaf.
Qed.

Lemma ConvYyBcAs: ↓ yingYangBcAs.
Proof.
  decomp; apply ConvNode; apply ConvYyAsBc.
Qed.

(* Lemmas on Always Convergence of strategy profiles *)
Lemma AlwsConvYyAcBs: ⇓ yingYangAcBs.
Proof.
  cofix AlwsConvYyAcBs;
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvYyBsAc | 
   induction c'; [apply AlwaysLeaf | decomp; apply AlwaysNode; [apply ConvNode; apply ConvLeaf |
                                                                 induction c'; [apply AlwaysLeaf | apply AlwsConvYyAcBs]]]].
Qed.

Lemma AlwsConvYyBsAc: ⇓ yingYangBsAc.
Proof.
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvLeaf |
   induction c'; [apply AlwaysLeaf | apply AlwsConvYyAcBs]].
Qed.

Lemma AlwsConvYyBcAs: ⇓ yingYangBcAs.
Proof.
  cofix AlwsConvYyBcAs;
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvYyAsBc |
   induction c'; [apply AlwaysLeaf |
                   decomp; apply AlwaysNode;
                   [apply ConvNode; apply ConvLeaf|
                    induction c'; [apply AlwaysLeaf | apply AlwsConvYyBcAs]]]].
Qed.

Lemma AlwsConvYyAsBc: ⇓ yingYangAsBc.
Proof.
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvLeaf |
   induction c'; [apply AlwaysLeaf | apply AlwsConvYyBcAs]].
Qed.

(* Equality of the underlying game *) 
Lemma sameGameBcAc_BsAc: game yingYangBcAc == game yingYangBsAc.
Proof.
  cofix sameGameBcAc_BsAc.
  rewrite <- StratProf_decomposition with (s:=yingYangBcAc);
    rewrite <- StratProf_decomposition with (s:=yingYangBsAc);
  cbn;
  rewrite gameNode; rewrite gameNode; apply gEqualNode;
  induction c; 
  [apply refGEqual |
   rewrite <- StratProf_decomposition with (s:=yingYangAcBc);
     rewrite <- StratProf_decomposition with (s:=yingYangAcBs);
     simpl;
     rewrite gameNode; rewrite gameNode; apply gEqualNode;
     induction c; [apply refGEqual | apply sameGameBcAc_BsAc]].
Qed.

Lemma sameGameAcBc_AcBs: game yingYangAcBc == game yingYangAcBs.
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangAcBc);
  rewrite <- StratProf_decomposition with (s:=yingYangAcBs);
  simpl.
  rewrite gameNode; rewrite gameNode; apply gEqualNode.
  induction c; [apply refGEqual | apply sameGameBcAc_BsAc].
Qed.

Lemma sameGameBcAs_BcAc: game yingYangBcAc == game yingYangBcAs.
Proof.
  cofix sameGameBcAc_BsAc.
  rewrite <- StratProf_decomposition with (s:=yingYangBcAc);
  rewrite <- StratProf_decomposition with (s:=yingYangBcAs);
  simpl.
  rewrite gameNode; rewrite gameNode; apply gEqualNode.
  induction c.
  apply refGEqual.
  rewrite <- StratProf_decomposition with (s:=yingYangAcBc);
  rewrite <- StratProf_decomposition with (s:=yingYangAsBc);
  simpl.
  rewrite gameNode; rewrite gameNode; apply gEqualNode.
  induction c; [apply refGEqual | apply sameGameBcAc_BsAc].
Qed.

Lemma sameGameAcBc_AsBc: game yingYangAcBc == game yingYangAsBc.
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangAcBc);
  rewrite <- StratProf_decomposition with (s:=yingYangAsBc);
  simpl.
  rewrite gameNode; rewrite gameNode; apply gEqualNode.
  induction c; [apply refGEqual | apply sameGameBcAs_BcAc].
Qed.

(* SPE *)
Lemma SPEYyAcBs: SPE eqYY yingYangAcBs.
Proof.
  cofix SPEYyAcBs;
  decomp;
  apply SPENode with (c':=right)(u:=[ying,yang])(u':=[ying,yang]);
  [apply AlwaysNode;  [apply ConvNode; apply ConvYyBsAc | 
                      induction c';  [apply AlwaysLeaf | apply AlwsConvYyBsAc]] |
   apply UassignYyBsAc |
   apply UassignYyBsAc |
   reflexivity |
   decomp; apply SPENode with (c':=right)(u:=[ying,yang])(u':=[ying,yang]);
   [apply AlwaysNode; [apply ConvNode; apply ConvLeaf |
                       induction c'; [apply AlwaysLeaf | apply AlwsConvYyAcBs]] |
    apply UassignYyAcBs |
    apply UassignLeaf |
    reflexivity |
    apply SPEYyAcBs]].
Qed.

Lemma SPEYyBsAc: SPE eqYY yingYangBsAc.
Proof.
  cofix SPEYyBsAc.
  decomp;
  apply SPENode with (c':=right)(u:=[ying,yang])(u':=[ying,yang]);
  [apply AlwaysNode; [apply ConvNode; apply ConvLeaf | 
                      induction c'; [apply AlwaysLeaf | apply AlwsConvYyAcBs]] |
  apply UassignYyAcBs |
  apply UassignLeaf |
  reflexivity |
  apply SPEYyAcBs].
Qed.

Lemma SPEYyAsBc: SPE eqYY yingYangAsBc.
Proof.
  cofix SPEYyAsBc.
  decomp.
  apply SPENode with (c':=right)(u:=[yang,ying])(u':=[yang,ying]).
  apply AlwaysNode.  
  apply ConvNode.
  apply ConvLeaf.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyBcAs.
  apply UassignYyBcAs.
  apply UassignLeaf.
  reflexivity.
  decomp.
  apply SPENode with (c':=right)(u:=[yang,ying])(u':=[yang,ying]).
  apply AlwaysNode.  
  apply ConvNode.  
  apply ConvYyAsBc.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyAsBc.
  apply UassignYyAsBc.
  apply UassignYyAsBc.
  reflexivity.
  apply SPEYyAsBc.
Qed.

Lemma SPEYyBcAs: SPE eqYY yingYangBcAs.
Proof.
  decomp.
  apply SPENode with (c':=right)(u:=[yang,ying])(u':=[yang,ying]).
  apply AlwaysNode.  
  apply ConvNode.
  apply ConvYyAsBc.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyAsBc.
  apply UassignYyAsBc.
  apply UassignYyAsBc.
  reflexivity.
  apply SPEYyAsBc.
Qed.

(* Good *)
Lemma GoodYyAcBc: good eqYY yingYangAcBc.
Proof.
  decomp.
  apply goodNode with (next':= <<[yang,ying]>> +++ yingYangBsAc).
  rewrite gameNode; rewrite gameNode.
  apply gEqualNode.
  induction c.
  rewrite gameLeaf.
  apply gEqualLeaf.
  apply sameGameBcAc_BsAc.
  apply SPENode with (c':=right)(u:=[ying,yang])(u':=[ying,yang]).
  apply AlwaysNode.
  apply ConvNode.
  apply ConvYyBsAc.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyBsAc.
  apply UassignYyBsAc.
  apply UassignYyBsAc.
  reflexivity.
  apply SPEYyBsAc.
Qed.

Lemma GoodYyBcAc: good eqYY yingYangBcAc.
Proof.
  decomp.
  apply goodNode with (next':= <<[ying,yang]>> +++ yingYangAsBc).
  rewrite gameNode; rewrite gameNode.
  apply gEqualNode.
  induction c.
  rewrite gameLeaf.
  apply gEqualLeaf.
  apply sameGameAcBc_AsBc.
  apply SPENode with (c':=right)(u:=[yang,ying])(u':=[yang,ying]).
  apply AlwaysNode.
  apply ConvNode.
  apply ConvYyAsBc.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyAsBc.
  apply UassignYyAsBc.
  apply UassignYyAsBc.
  reflexivity.
  apply SPEYyAsBc.
Qed.

(* Always Good AcBc *)
Lemma AlongGoodYyAcBc: AlongGood eqYY yingYangAcBc.
Proof.
  cofix AlwaysGoodYyAcBc.
  decomp.
  apply AlongNode.
  replace (<< Alice, right, << [yang,ying] >> +++ yingYangBcAc >>) with yingYangAcBc.
  apply GoodYyAcBc.
  rewrite <- StratProf_decomposition with (s:=yingYangAcBc); simpl; reflexivity.
  decomp.
  apply AlongNode.
  replace (<< Bob, right, << [ying,yang] >> +++ yingYangAcBc >>) with yingYangBcAc.
  apply GoodYyBcAc.
  rewrite <- StratProf_decomposition with (s:=yingYangBcAc); simpl; reflexivity.
  apply AlwaysGoodYyAcBc.
Qed.

(* Divergent *)
Lemma DivergenceYyAcBc: ↑ yingYangAcBc.
Proof.
  cofix DivergenceYyAcBc.
  decomp.
  apply divNode.
  decomp.
  apply divNode.
  apply DivergenceYyAcBc.
Qed.

End YingYang.