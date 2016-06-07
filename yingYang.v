(* Time-stamp: "2016-05-06 09:15:34 pierre" *)
(****************************************************************)
(*                       yingYang.v                             *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.4pl4               January -- May   2016   *)
(****************************************************************)
Section YingYang.

Add LoadPath ".". 

Require Import games.

(* Setting sets for agents and choices *)
Inductive AliceBob : Set := | Alice | Bob.
Inductive DorR : Set := | d | r.
Inductive YingYang: Set := | ying | yang.
Definition Choice: AliceBob -> Set := fun a => DorR.

Arguments StratProf [Agent Choice Utility].
Arguments Game [Agent Choice Utility].
Arguments UAssignment [Agent Choice Utility] s H a.
Arguments game [Agent Choice Utility] s.
Arguments StratProf_decomposition [Agent Choice Utility] s.
Arguments Convergent [Agent Choice Utility] s.
Arguments AlwaysConvergent [Agent Choice Utility] s.
Arguments convLeaf [Agent Choice Utility] f.
Arguments convNode [Agent Choice Utility] a c next _.
Arguments SPE [Agent Choice Utility] preference  s.
Arguments Uassign [Agent Choice Utility] s a u.
Arguments good [Agent Choice Utility] preference s.
Arguments gEqual [Agent Choice Utility] g1 g2.
Arguments Divergent  [Agent Choice Utility] s.
Arguments AlwaysGood  [Agent Choice Utility] preference s.

Notation "<< f >>" := (sLeaf AliceBob Choice YingYang  f).
Notation "<< a , c , next >>" := 
  (sNode AliceBob Choice YingYang a c next).
Notation "[ x , y ]" := 
  (fun a:AliceBob => match a with Alice => x | Bob => y end).
Notation "<| f |>" := (gLeaf  AliceBob Choice YingYang f).
Notation "<| a , next |>" := (gNode AliceBob Choice YingYang a next).

Notation "s1 +++ s2" := 
  (fun c:DorR => match c with d => s1 | r => s2 end) 
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
CoFixpoint yingYangAcBs := <<Alice, r, <<[yang,ying]>> +++ yingYangBsAc>>
  with yingYangBsAc := <<Bob, d, <<[ying,yang]>> +++ yingYangAcBs>>.

CoFixpoint yingYangAsBc := <<Alice, d, <<[yang,ying]>> +++ yingYangBcAs>>
  with yingYangBcAs := <<Bob, r, <<[ying,yang]>> +++ yingYangAsBc>>.

CoFixpoint yingYangAcBc := <<Alice, r, <<[yang,ying]>> +++ yingYangBcAc>>
  with yingYangBcAc := <<Bob, r, <<[ying,yang]>> +++ yingYangAcBc>>.

(* == Lemmas on utility assignments == *)

(* A continue Bob stops *)

Lemma UassignYyBsAcya: Uassign yingYangBsAc Alice ying.
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangBsAc); simpl.
  apply UassignNode.
  apply UassignLeaf.
Qed.

Lemma UassignYyBsAcyi: Uassign yingYangBsAc Bob yang.
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangBsAc); simpl.
  apply UassignNode.
  apply UassignLeaf.
Qed.

Lemma UassignYyAcBsyi: Uassign yingYangAcBs Bob yang.
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangAcBs); simpl.
  apply UassignNode.
  apply UassignYyBsAcyi.
Qed.

(* A stops Bob continues *)
Lemma UassignYyAsBcyi: Uassign yingYangAsBc Alice yang.
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangAsBc); simpl.
  apply UassignNode.
  apply UassignLeaf.
Qed.

Lemma UassignYyAsBcya: Uassign yingYangAsBc Bob ying.
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangAsBc); simpl.
  apply UassignNode.
  apply UassignLeaf.
Qed.

Lemma UassignYyBcAsyi: Uassign yingYangBcAs Alice yang.
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangBcAs); simpl.
  apply UassignNode.
  apply UassignYyAsBcyi.
Qed.

Lemma UassignYyBcAsya:  Uassign yingYangBcAs Bob ying.
Proof.
  rewrite <- StratProf_decomposition with (s:=yingYangBcAs); simpl.
  apply UassignNode.
  apply UassignYyAsBcya.
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
  simpl;
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
Lemma SPEYyAcBs: SPE eq yingYangAcBs.
Proof.
  cofix SPEYyAcBs;
  decomp;
  apply SPENode with (c':=r)(u:=ying)(u':=ying);
  [apply AlwaysNode; [apply ConvNode; apply ConvYyBsAc |
                      induction c';  [apply AlwaysLeaf | apply AlwsConvYyBsAc]] |
   apply UassignYyBsAcya |
   apply UassignYyBsAcya | 
   reflexivity |
   decomp ; apply SPENode with (c':=r)(u:=yang)(u':=yang); 
   [apply AlwaysNode; [apply ConvNode; apply ConvLeaf |
                       induction c'; [apply AlwaysLeaf | apply AlwsConvYyAcBs]] |
    apply UassignYyAcBsyi |
    apply UassignLeaf |
    reflexivity |
    apply SPEYyAcBs]].
Qed.

Lemma SPEYyBsAc: SPE eq yingYangBsAc.
Proof.
  cofix SPEYyBsAc.
  decomp.
  apply SPENode with (c':=r)(u:=yang)(u':=yang).
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

Lemma SPEYyAsBc: SPE eq yingYangAsBc.
Proof.
  cofix SPEYyAsBc.
  decomp.
  apply SPENode with (c':=r)(u:=yang)(u':=yang).
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
  apply SPENode with (c':=r)(u:=ying)(u':=ying).
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

Lemma SPEYyBcAs: SPE eq yingYangBcAs.
Proof.
  decomp.
  apply SPENode with (c':=r)(u:=ying)(u':=ying).
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
Lemma GoodYyAcBc: good eq yingYangAcBc.
Proof.
  decomp.
  apply goodNode with (next':= <<[yang,ying]>> +++ yingYangBsAc).
  split.
  rewrite gameNode; rewrite gameNode.
  apply gEqualNode.
  induction c.
  rewrite gameLeaf.
  apply gEqualLeaf.
  apply sameGameBcAc_BsAc.
  apply SPENode with (c':=r)(u:=ying)(u':=ying).
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

Lemma GoodYyBcAc: good eq yingYangBcAc.
Proof.
  decomp.
  apply goodNode with (next':= <<[ying,yang]>> +++ yingYangAsBc).
  split.
  rewrite gameNode; rewrite gameNode.
  apply gEqualNode.
  induction c.
  rewrite gameLeaf.
  apply gEqualLeaf.
  apply sameGameAcBc_AsBc.
  apply SPENode with (c':=r)(u:=ying)(u':=ying).
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
Lemma AlwaysGoodYyAcBc: AlwaysGood eq yingYangAcBc.
Proof.
  cofix AlwaysGoodYyAcBc.
  decomp.
  apply AlwaysNode.
  replace (<< Alice, r, << [yang,ying] >> +++ yingYangBcAc >>) with yingYangAcBc.
  apply GoodYyAcBc.
  rewrite <- StratProf_decomposition with (s:=yingYangAcBc); simpl; reflexivity.
  induction c'.
  apply AlwaysLeaf.
  decomp.
  apply AlwaysNode.
  replace (<< Bob, r, << [ying,yang] >> +++ yingYangAcBc >>) with yingYangBcAc.
  apply GoodYyBcAc.
  rewrite <- StratProf_decomposition with (s:=yingYangBcAc); simpl; reflexivity.
  induction c'; [apply AlwaysLeaf | apply AlwaysGoodYyAcBc].
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