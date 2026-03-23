Record cat :=
  mk_cat {
      ob: Type;
      hom: ob -> ob -> Type;
      comp {a b c: ob}: hom a b -> hom b c -> hom a c;
      id (a: ob): hom a a;
      
      assoc {a b c d: ob} (f: hom a b) (g: hom b c) (h: hom c d)
      : comp f (comp g h) = comp (comp f g) h;
    }.

Definition empty_cat :=
  mk_cat Empty_set (fun _ _ => Empty_set)
         (fun a _ _ _ _ => match a with end)
         (fun a => match a with end)
         (fun a _ _ _ _ _ _ => eq_refl _).

