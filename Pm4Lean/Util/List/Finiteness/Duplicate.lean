import Pm4Lean.Util.List.Duplicate
import Pm4Lean.Util.List.Finiteness.Bounds

namespace Pm4Lean

namespace List

theorem hasDuplicate_of_length_gt_length_of_subset
    {α : Type u} [BEq α] [LawfulBEq α]
    {xs univList : List α}
    (hLen : univList.length < xs.length)
    (hSubset : ∀ a : α, a ∈ xs → a ∈ univList) :
    HasDuplicate xs :=
  hasDuplicate_of_not_nodup
    (not_nodup_of_length_gt_length_of_subset hLen hSubset)

end List
end Pm4Lean
