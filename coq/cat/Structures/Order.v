Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat Functor TypeC Preorder.
  
Open Scope cat_scope.
Open Scope order_scope.

Record partial_order :=
  {
    partial_preorder:> preorder;
    le_antisym (x y: partial_preorder.(X)): x <= y -> y <= x -> x = y;
  }.

Arguments le_antisym {p x y}.

Definition cat_partial_order: cat.
  refine {|
      ob := partial_order;
      hom := preorder_hom;
      id := preorder_hom_id;
      comp := @preorder_hom_comp;
    |}; intros; apply preorder_hom_ext; reflexivity.
Defined.

Record total_order :=
  {
    total_partial:> partial_order;
    le_total (x y: total_partial.(X)): x <= y \/ y <= x;
  }.

Definition cat_total_order: cat.
  refine {|
      ob := total_order;
      hom := preorder_hom;
      id := preorder_hom_id;
      comp := @preorder_hom_comp;
    |}; intros; apply preorder_hom_ext; reflexivity.
Defined.
