/- Port of execution/theories/ChainedList.v -/

namespace ConCert.Execution.ChainedList

inductive ChainedList {Point : Type} (Link : Point → Point → Type) : Point → Point → Type where
  | clnil {p} : ChainedList Link p p
  | snoc {frm mid to_} :
      ChainedList Link frm mid → Link mid to_ → ChainedList Link frm to_

def clist_app {Point : Type} {Link : Point → Point → Type}
    {frm mid to_ : Point}
    (xs : ChainedList Link frm mid)
    (ys : ChainedList Link mid to_) : ChainedList Link frm to_ :=
  match ys with
  | ChainedList.clnil      => xs
  | ChainedList.snoc ys' y => ChainedList.snoc (clist_app xs ys') y

def clist_prefix {Point : Type} {Link : Point → Point → Type}
    {frm mid to_ : Point}
    (pfx : ChainedList Link frm mid)
    (full : ChainedList Link frm to_) : Prop :=
  ∃ sfx, full = clist_app pfx sfx

def clist_suffix {Point : Type} {Link : Point → Point → Type}
    {frm mid to_ : Point}
    (sfx : ChainedList Link mid to_)
    (full : ChainedList Link frm to_) : Prop :=
  ∃ pfx, full = clist_app pfx sfx

axiom app_clnil_l :
  ∀ {Point : Type} {Link : Point → Point → Type}
    {frm to_ : Point} (xs : ChainedList Link frm to_),
    clist_app ChainedList.clnil xs = xs

axiom clist_app_assoc :
  ∀ {Point : Type} {Link : Point → Point → Type}
    {c1 c2 c3 c4 : Point}
    (xs : ChainedList Link c1 c2)
    (ys : ChainedList Link c2 c3)
    (zs : ChainedList Link c3 c4),
    clist_app xs (clist_app ys zs) = clist_app (clist_app xs ys) zs

axiom prefix_of_app :
  ∀ {Point : Type} {Link : Point → Point → Type}
    {frm mid to_ to_' : Point}
    {pfx : ChainedList Link frm mid}
    {xs : ChainedList Link frm to_}
    {sfx : ChainedList Link to_ to_'},
    clist_prefix pfx xs →
    clist_prefix pfx (clist_app xs sfx)

end ConCert.Execution.ChainedList
