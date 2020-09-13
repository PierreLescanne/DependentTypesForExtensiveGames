(* Time-stamp: "2018-02-09 17:01:14 pierre" *)
(****************************************************************)
(*                       yinYang.v                             *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.4pl4               January -- May   2016   *)
(****************************************************************)

Require Import games_Choice_Dependent.

Section YinYang.

(* Setting sets for agents and choices *)
Inductive AliceBob : Set := | Alice | Bob.
Inductive DorR : Set := | down | right.
Inductive YinYang: Set := | ying | yang.
Definition Choice: AliceBob -> Set := fun a => DorR.

Arguments StratProf {Agent Utility Choice}.
Arguments Game {Agent Utility Choice}.
Arguments UAssignment [Agent Utility Choice] s H a.
Arguments game [Agent Utility Choice] s.
Arguments StratProf_decomposition [Agent Utility Choice] s.
Arguments Convergent [Agent Utility Choice] s.
Arguments AlwaysConvergent [Agent Utility Choice] s.
Arguments convLeaf [Agent Utility Choice] f.
Arguments convNode [Agent Utility Choice] a c next _.
Arguments SPE [Agent Utility Choice] preference  s.
Arguments Uassign [Agent Utility Choice] s a u.
Arguments good [Agent Utility Choice] preference s.
Arguments gEqual [Agent Utility Choice] g1 g2.
Arguments Divergent  [Agent Utility Choice] s.
Arguments AlwaysGood  [Agent Utility Choice] preference s.

Notation "<< f >>" := (sLeaf AliceBob YinYang Choice  f).
Notation "<< a , c , next >>" := 
  (sNode AliceBob YinYang Choice a c next).
Notation "[ x , y ]" := 
  (fun a:AliceBob => match a with Alice => x | Bob => y end).
Notation "<| f |>" := (gLeaf  AliceBob YinYang Choice f).
Notation "<| a , next |>" := (gNode AliceBob YinYang Choice a next).

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
CoFixpoint yinYangAcBs := <<Alice, right, <<[yang,ying]>> +++ yinYangBsAc>>
  with yinYangBsAc := <<Bob, down, <<[ying,yang]>> +++ yinYangAcBs>>.

CoFixpoint yinYangAsBc := <<Alice, down, <<[yang,ying]>> +++ yinYangBcAs>>
  with yinYangBcAs := <<Bob, right, <<[ying,yang]>> +++ yinYangAsBc>>.

CoFixpoint yinYangAcBc := <<Alice, right, <<[yang,ying]>> +++ yinYangBcAc>>
  with yinYangBcAc := <<Bob, right, <<[ying,yang]>> +++ yinYangAcBc>>.

(* == Lemmas on utility assignments == *)

(* A continue Bob stops *)

Lemma UassignYyBsAcya: Uassign yinYangBsAc Alice ying.
Proof.
  rewrite <- StratProf_decomposition with (s:=yinYangBsAc); simpl.
  apply UassignNode.
  apply UassignLeaf.
Qed.

Lemma UassignYyBsAcyi: Uassign yinYangBsAc Bob yang.
Proof.
  rewrite <- StratProf_decomposition with (s:=yinYangBsAc); simpl.
  apply UassignNode.
  apply UassignLeaf.
Qed.

Lemma UassignYyAcBsyi: Uassign yinYangAcBs Bob yang.
Proof.
  rewrite <- StratProf_decomposition with (s:=yinYangAcBs); simpl.
  apply UassignNode.
  apply UassignYyBsAcyi.
Qed.

(* A stops Bob continues *)
Lemma UassignYyAsBcyi: Uassign yinYangAsBc Alice yang.
Proof.
  rewrite <- StratProf_decomposition with (s:=yinYangAsBc); simpl.
  apply UassignNode.
  apply UassignLeaf.
Qed.

Lemma UassignYyAsBcya: Uassign yinYangAsBc Bob ying.
Proof.
  rewrite <- StratProf_decomposition with (s:=yinYangAsBc); simpl.
  apply UassignNode.
  apply UassignLeaf.
Qed.

Lemma UassignYyBcAsyi: Uassign yinYangBcAs Alice yang.
Proof.
  rewrite <- StratProf_decomposition with (s:=yinYangBcAs); simpl.
  apply UassignNode.
  apply UassignYyAsBcyi.
Qed.

Lemma UassignYyBcAsya:  Uassign yinYangBcAs Bob ying.
Proof.
  rewrite <- StratProf_decomposition with (s:=yinYangBcAs); simpl.
  apply UassignNode.
  apply UassignYyAsBcya.
Qed.

(* Lemmas on Convergence of strategy profiles *)
Lemma ConvYyBsAc: ↓ yinYangBsAc.
Proof.
  decomp.
  apply ConvNode.
  apply ConvLeaf.
Qed.

Lemma ConvYyAcBs: ↓ yinYangAcBs.
Proof.
  decomp.
  decomp.
  apply ConvNode.
  apply ConvYyBsAc.
Qed.

Lemma ConvYyAsBc: ↓ yinYangAsBc.
Proof.
  decomp;apply ConvNode; apply ConvLeaf.
Qed.

Lemma ConvYyBcAs: ↓ yinYangBcAs.
Proof.
  decomp; apply ConvNode; apply ConvYyAsBc.
Qed.

(* Lemmas on Always Convergence of strategy profiles *)
Lemma AlwsConvYyAcBs: ⇓ yinYangAcBs.
Proof.
  cofix AlwsConvYyAcBs;
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvYyBsAc | 
   induction c'; [apply AlwaysLeaf | decomp; apply AlwaysNode; [apply ConvNode; apply ConvLeaf |
                                                                 induction c'; [apply AlwaysLeaf | apply AlwsConvYyAcBs]]]].
Qed.

Lemma AlwsConvYyBsAc: ⇓ yinYangBsAc.
Proof.
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvLeaf |
   induction c'; [apply AlwaysLeaf | apply AlwsConvYyAcBs]].
Qed.

Lemma AlwsConvYyBcAs: ⇓ yinYangBcAs.
Proof.
  cofix AlwsConvYyBcAs;
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvYyAsBc |
   induction c'; [apply AlwaysLeaf |
                   decomp; apply AlwaysNode;
                   [apply ConvNode; apply ConvLeaf|
                    induction c'; [apply AlwaysLeaf | apply AlwsConvYyBcAs]]]].
Qed.

Lemma AlwsConvYyAsBc: ⇓ yinYangAsBc.
Proof.
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvLeaf |
   induction c'; [apply AlwaysLeaf | apply AlwsConvYyBcAs]].
Qed.

(* Equality of the underlying game *) 
Lemma sameGameBcAc_BsAc: game yinYangBcAc == game yinYangBsAc.
Proof.
  cofix sameGameBcAc_BsAc.
  rewrite <- StratProf_decomposition with (s:=yinYangBcAc);
  rewrite <- StratProf_decomposition with (s:=yinYangBsAc);
  simpl;
  rewrite gameNode; rewrite gameNode; apply gEqualNode;
  induction c; 
  [apply refGEqual |
   rewrite <- StratProf_decomposition with (s:=yinYangAcBc);
     rewrite <- StratProf_decomposition with (s:=yinYangAcBs);
     simpl;
     rewrite gameNode; rewrite gameNode; apply gEqualNode;
     induction c; [apply refGEqual | apply sameGameBcAc_BsAc]].
Qed.

Lemma sameGameAcBc_AcBs: game yinYangAcBc == game yinYangAcBs.
Proof.
  rewrite <- StratProf_decomposition with (s:=yinYangAcBc);
  rewrite <- StratProf_decomposition with (s:=yinYangAcBs);
  simpl.
  rewrite gameNode; rewrite gameNode; apply gEqualNode.
  induction c; [apply refGEqual | apply sameGameBcAc_BsAc].
Qed.

Lemma sameGameBcAs_BcAc: game yinYangBcAc == game yinYangBcAs.
Proof.
  cofix sameGameBcAc_BsAc.
  rewrite <- StratProf_decomposition with (s:=yinYangBcAc);
  rewrite <- StratProf_decomposition with (s:=yinYangBcAs);
  simpl.
  rewrite gameNode; rewrite gameNode; apply gEqualNode.
  induction c.
  apply refGEqual.
  rewrite <- StratProf_decomposition with (s:=yinYangAcBc);
  rewrite <- StratProf_decomposition with (s:=yinYangAsBc);
  simpl.
  rewrite gameNode; rewrite gameNode; apply gEqualNode.
  induction c; [apply refGEqual | apply sameGameBcAc_BsAc].
Qed.

Lemma sameGameAcBc_AsBc: game yinYangAcBc == game yinYangAsBc.
Proof.
  rewrite <- StratProf_decomposition with (s:=yinYangAcBc);
  rewrite <- StratProf_decomposition with (s:=yinYangAsBc);
  simpl.
  rewrite gameNode; rewrite gameNode; apply gEqualNode.
  induction c; [apply refGEqual | apply sameGameBcAs_BcAc].
Qed.

(* SPE *)
Lemma SPEYyAcBs: SPE eq yinYangAcBs.
Proof.
  cofix SPEYyAcBs;
  decomp;
  apply SPENode with (c':=right)(u:=ying)(u':=ying);
  [apply AlwaysNode; [apply ConvNode; apply ConvYyBsAc |
                      induction c';  [apply AlwaysLeaf | apply AlwsConvYyBsAc]] |
   apply UassignYyBsAcya |
   apply UassignYyBsAcya | 
   reflexivity |
   decomp ; apply SPENode with (c':=right)(u:=yang)(u':=yang); 
   [apply AlwaysNode; [apply ConvNode; apply ConvLeaf |
                       induction c'; [apply AlwaysLeaf | apply AlwsConvYyAcBs]] |
    apply UassignYyAcBsyi |
    apply UassignLeaf |
    reflexivity |
    apply SPEYyAcBs]].
Qed.

Lemma SPEYyBsAc: SPE eq yinYangBsAc.
Proof.
  cofix SPEYyBsAc.
  decomp.
  apply SPENode with (c':=right)(u:=yang)(u':=yang).
  apply AlwaysNode.  
  apply ConvNode.
  apply ConvLeaf.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyAcBs.
  apply UassignYyAcBsyi.
  apply UassignLeaf.
  reflexivity.
  apply SPEYyAcBs.
Qed.

Lemma SPEYyAsBc: SPE eq yinYangAsBc.
Proof.
  cofix SPEYyAsBc.
  decomp.
  apply SPENode with (c':=right)(u:=yang)(u':=yang).
  apply AlwaysNode.  
  apply ConvNode.
  apply ConvLeaf.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyBcAs.
  apply UassignYyBcAsyi.
  apply UassignLeaf.
  reflexivity.
  decomp.
  apply SPENode with (c':=right)(u:=ying)(u':=ying).
  apply AlwaysNode.  
  apply ConvNode.  
  apply ConvYyAsBc.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyAsBc.
  apply UassignYyAsBcya.
  apply UassignYyAsBcya.
  reflexivity.
  apply SPEYyAsBc.
Qed.

Lemma SPEYyBcAs: SPE eq yinYangBcAs.
Proof.
  decomp.
  apply SPENode with (c':=right)(u:=ying)(u':=ying).
  apply AlwaysNode.  
  apply ConvNode.
  apply ConvYyAsBc.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyAsBc.
  apply UassignYyAsBcya.
  apply UassignYyAsBcya.
  reflexivity.
  apply SPEYyAsBc.
Qed.

(* Good *)
Lemma GoodYyAcBc: good eq yinYangAcBc.
Proof.
  decomp.
  apply goodNode with (next':= <<[yang,ying]>> +++ yinYangBsAc).
  split.
  rewrite gameNode; rewrite gameNode.
  apply gEqualNode.
  induction c.
  rewrite gameLeaf.
  apply gEqualLeaf.
  apply sameGameBcAc_BsAc.
  apply SPENode with (c':=right)(u:=ying)(u':=ying).
  apply AlwaysNode.
  apply ConvNode.
  apply ConvYyBsAc.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyBsAc.
  apply UassignYyBsAcya.
  apply UassignYyBsAcya.
  reflexivity.
  apply SPEYyBsAc.
Qed.

Lemma GoodYyBcAc: good eq yinYangBcAc.
Proof.
  decomp.
  apply goodNode with (next':= <<[ying,yang]>> +++ yinYangAsBc).
  split.
  rewrite gameNode; rewrite gameNode.
  apply gEqualNode.
  induction c.
  rewrite gameLeaf.
  apply gEqualLeaf.
  apply sameGameAcBc_AsBc.
  apply SPENode with (c':=right)(u:=ying)(u':=ying).
  apply AlwaysNode.
  apply ConvNode.
  apply ConvYyAsBc.
  induction c'.
  apply AlwaysLeaf.
  apply AlwsConvYyAsBc.
  apply UassignYyAsBcya.
  apply UassignYyAsBcya.
  reflexivity.
  apply SPEYyAsBc.
Qed.

(* Always Good AcBc *)
Lemma AlwaysGoodYyAcBc: AlwaysGood eq yinYangAcBc.
Proof.
  cofix AlwaysGoodYyAcBc.
  decomp.
  apply AlwaysNode.
  replace (<< Alice, right, << [yang,ying] >> +++ yinYangBcAc >>) with yinYangAcBc.
  apply GoodYyAcBc.
  rewrite <- StratProf_decomposition with (s:=yinYangAcBc); simpl; reflexivity.
  induction c'.
  apply AlwaysLeaf.
  decomp.
  apply AlwaysNode.
  replace (<< Bob, right, << [ying,yang] >> +++ yinYangAcBc >>) with yinYangBcAc.
  apply GoodYyBcAc.
  rewrite <- StratProf_decomposition with (s:=yinYangBcAc); simpl; reflexivity.
  induction c'; [apply AlwaysLeaf | apply AlwaysGoodYyAcBc].
Qed.

(* Divergent *)
Lemma DivergenceYyAcBc: ↑ yinYangAcBc.
Proof.
  cofix DivergenceYyAcBc.
  decomp.
  apply divNode.
  decomp.
  apply divNode.
  apply DivergenceYyAcBc.
Qed.

End YinYang.
