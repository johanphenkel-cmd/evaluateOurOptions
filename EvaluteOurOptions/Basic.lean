--MergeSort
def myMerge {α} (le : α → α → Bool) (xs ys : Array α) (ix iy : Nat) (work : Array α) (hwork : work.size = xs.size + ys.size) (hix : ix ≤ xs.size) (hiy : iy ≤ ys.size): { merged : Array α // merged.size = work.size } :=
  if hix : ix < xs.size then
    if hiy : iy < ys.size then
      if le xs[ix] ys[iy]
        then ⟨myMerge le xs ys (ix + 1) iy (work.set (ix+iy) xs[ix]) (by grind) (by grind) (by grind), (by grind)⟩
        else ⟨myMerge le xs ys ix (iy + 1) (work.set (ix+iy) ys[iy]) (by grind) (by grind) (by grind), (by grind)⟩
    else
      ⟨myMerge le xs ys (ix + 1) iy (work.set (ix+iy) xs[ix]) (by grind) (by grind) (by grind), (by grind)⟩
  else
    if hiy : iy < ys.size then
      ⟨myMerge le xs ys ix (iy + 1) (work.set (ix+iy) ys[iy]) (by grind) (by grind) (by grind), (by grind)⟩
    else
      ⟨work, rfl⟩

def myMergeSort1 (xs aux : Array α) (le : α → α → Bool) (haux : xs.size = aux.size): { sorted : Array α // sorted.size = xs.size } :=
  if h : xs.size ≤ 1
  then ⟨xs, rfl⟩
  else
    let mid := xs.size / 2
    let left := myMergeSort1 (xs.take mid) (aux.take mid) le (by grind)
    let right := myMergeSort1 (xs.drop mid) (aux.drop mid) le (by grind)
    have hlr : aux.size = left.val.size + right.val.size := by grind
    ⟨myMerge le left.val right.val 0 0 aux hlr (by grind) (by grind), (by grind)⟩


def le_Nat (x y : Nat): Bool := x ≤ y
def testValues : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41]
#eval myMergeSort1 testValues testValues le_Nat rfl
--this is not tail-recursive, so left and right are newly allocated every time!
