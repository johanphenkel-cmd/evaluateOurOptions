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
--> New idea: Bottom-up mergesort

def copyFinalSlice (inp out : Array α) (start : Nat) : Array α :=
  if h : start < inp.size then --arrived at end?
    copyFinalSlice inp (out.set! start inp[start]) (start + 1) --copy current value to same position in out, increase current index
  else
    out --if there is nothing left to copy, return

def myMerge_sliced {α} [Inhabited α] (le : α → α → Bool) (inp : Array α) (start mid last ix iy : Nat) (work : Array α) : Array α := --variation of myMerge w/o indexing proofs and on two full arrays, replacing xs and ys by slicing indices
  if ix < (mid - start) then --xs finished? (ix < len xs)
    if iy < (last - mid) then --ys finished? (iy < len ys)
      if le inp[start+ix]! inp[mid+iy]! --comparison
        then myMerge_sliced le inp start mid last (ix + 1) iy (work.set! (ix+iy+start) inp[start+ix]!) --if xs[ix] is smaller, it is written to the output at the correct location
        else myMerge_sliced le inp start mid last ix (iy + 1) (work.set! (ix+iy+start) inp[mid+iy]!) -- else, it's ys[iy]
    else
      myMerge_sliced le inp start mid last (ix + 1) iy (work.set! (ix+iy+start) inp[start+ix]!) --if ys is done, but not xs, the next element from xs is copied
  else
    if iy < (last - mid) then --ys finished?
      myMerge_sliced le inp start mid last ix (iy + 1) (work.set! (ix+iy+start) inp[mid+iy]!) --if xs is done, but not ys, the next element from ys is copied
    else
      work --if both slices are done, return

partial def mMS2_helper [Inhabited α] (le : α → α → Bool) (arr1 arr2 : Array α) (i width : Nat) : Array α :=
    if width < arr1.size then --outer loop: runs till the whole list has been merged over
      if i < arr1.size then --inner loop: goes through all the couples to merge, then increases i (the start marker) by the range that was just processed
        if i + width < arr1.size then --only merge if there is a counterpart to merge with
          if i + 2 * width > arr1.size then --if the counterpart is shorter, no problem, just use it
            mMS2_helper le arr1 (myMerge_sliced le arr1 i (i+width) arr1.size 0 0 arr2) (i+2*width) width --special case: counterpart is shorter
          else mMS2_helper le arr1 (myMerge_sliced le arr1 i (i+width) (i+2*width) 0 0 arr2) (i+2*width) width --normal case
        else mMS2_helper le arr1 (copyFinalSlice arr1 arr2 i) (i+2*width) width --special case: no counterpart => the already sorted portion is carried over
      else mMS2_helper le arr2 arr1 0 (2*width) --if all couples have been merged, switch arrays and merge those with their new counterparts
    else arr1

def myMergeSort2 [Inhabited α] (xs : Array α) (le : α → α → Bool) : Array α :=
  mMS2_helper le xs xs 0 1 --copy xs one time as an auxiliary array, initialise i and width


def testValues2 : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41, 88, 3, 65, 29, 54, 17, 72, 39, 84, 11, 63, 28, 95, 42, 7, 56, 31, 78, 19, 67, 44, 90, 25, 58, 14, 83, 37, 62, 9, 71, 48, 26, 93, 15, 52, 38, 77, 22, 69, 4, 86, 33, 61, 18, 45, 79, 12, 57, 35, 81, 24, 68, 43, 96, 8, 53, 27, 74, 16, 89, 41, 64, 30, 55, 20, 73, 46, 85, 10, 60, 36, 92, 21, 49, 66, 32, 75, 5, 87, 40, 59, 28, 70, 38, 94, 50, 80, 2, 97, 44]
#eval myMergeSort2 testValues2 le_Nat
#eval (myMergeSort1 testValues2 testValues2 le_Nat (by decide) = myMergeSort2 testValues2 le_Nat)

-- Quicksort
inductive Todo (α : Type) -- divides remaining objects into arrays left to sort and correct numbers
| Sort : Array α -> Todo α
| Push : α -> Todo α

def pivotselect [Ord α] (arr : Array α) : Option (α × Array α) := -- picks the median of first, middle (rounded down) and last element in array
  if h : arr.size = 0 then none
  else if h : arr.size < 3 then some (arr[0], arr.extract 1 arr.size) -- if array is smaller than 3 elements, primitively use first element
  else
    let size := arr.size
    let half := size/2
    let p1 := arr[0] -- first pivot: first element
    let p2 := arr[half] -- second pivot: middle element (rounded down)
    let p3 := arr[size-1] -- third pivot: last element
    let le := fun a b => compare a b != .gt -- use compare relying on Ord α instead of ≤ relying on LE α
    if le p1 p2 then -- find median, see cases
      if le p2 p3 then some (p2, (arr.extract 0 half) ++ (arr.extract (half+1) size)) -- p1 p2 p3 -> middle
      else if le p1 p3 then some (p3, arr.extract 0 (size-1)) -- p1 p3 p2 -> last
      else some (p1, arr.extract 1 size) -- p3 p1 p2 -> first
    else
      if le p1 p3 then some (p1, arr.extract 1 size) -- p2 p1 p3 -> first
      else if le p2 p3 then some (p3, arr.extract 0 (size-1)) -- p2 p3 p1 -> last
      else some (p2, (arr.extract 0 half) ++ (arr.extract (half+1) size)) -- p3 p2 p1 -> middle

partial def pivotsplitHelper [Ord α] (arr le gt : Array α) (pvt : α) : Array α × Array α := -- split array into less or equal and greater than pivot in one recursive pass
  let size := arr.size
  if h : size = 0 then (le, gt) -- if done then return
  else
    if compare arr[0] pvt != .gt then pivotsplitHelper (arr.extract 1 size) (le ++ #[arr[0]]) gt pvt -- not greater -> less or equal -> add to le
    else pivotsplitHelper (arr.extract 1 size) le (gt ++ #[arr[0]]) pvt -- greater -> add to gt

def pivotsplit [Ord α] (arr : Array α) (pvt : α) : Array α × Array α := -- initializes pivotsplitHelper with empty le/gt arrays
  pivotsplitHelper arr #[] #[] pvt

partial def quicksortHelper [Ord α] (todos : List (Todo α)) (acc : Array α) : Array α := -- recursively splits up arrays based on a pivot and schedules tasks using a todo list
  match todos with
  | [] => acc -- if nothing is left to do, return the result from the accumulator
  | inst :: rest =>
    match inst with
    | Todo.Push x => quicksortHelper rest (acc.push x) -- if the instruction is push, add the number to accumulator
    | Todo.Sort arr => -- if the instruction is sort, split the array based on a pivot into two more and leaves the pivot to be pushed
      match pivotselect arr with -- select a good pivot using pivotselect
      | none => quicksortHelper rest acc -- empty array to be sorted, ignore this
      | some (hd, #[]) => quicksortHelper rest (acc.push hd) -- if only one element, this element must be correct, so push directly
      | some (hd, tl) =>
        let (le, gt) := pivotsplit tl hd -- split array into less or equal than and greater than a pivot using pivotsplit
        let new := Todo.Sort le :: Todo.Push hd :: Todo.Sort gt :: rest -- schedule the tasks in todos
        quicksortHelper new acc -- recurse using the new todo list

def quicksort [Ord α] (arr : Array α) : Array α := -- initializes quicksortHelper with empty accumulator
  quicksortHelper [Todo.Sort arr] #[]

def demoArray1 : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41, 88, 3, 65, 29, 54, 17, 72, 39, 84, 11, 63, 28, 95, 42, 7, 56, 31, 78, 19, 67, 44, 90, 25, 58, 14, 83, 37, 62, 9, 71, 48, 26, 93, 15, 52, 38, 77, 22, 69, 4, 86, 33, 61, 18, 45, 79, 12, 57, 35, 81, 24, 68, 43, 96, 8, 53, 27, 74, 16, 89, 41, 64, 30, 55, 20, 73, 46, 85, 10, 60, 36, 92, 21, 49, 66, 32, 75, 5, 87, 40, 59, 28, 70, 38, 94, 50, 80, 2, 97, 44]
#eval quicksort demoArray1
def demoArray2 : Array String := #["Byte", "Gamma", "%", "Alpha", "·", "Beta", "Uranium", "$", "Aaron", "Xenon", "G", "e", "f(x)", "Über", "×"]
#eval quicksort demoArray2
