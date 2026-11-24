import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1

/-!
# Part I, `PartI:T04/10/1/2/1/8` (`WordSqSucc`)

Source of record: `the November 2 reference manuscript`, lines 285-287.
Pure combinatorics: the words of length `j+1` are `true :: u` and `false :: u` with `|u| = j`.
-/

set_option autoImplicit false

noncomputable section

open Set Finset

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

theorem wordSqSucc_proof : WordSqSucc := by
  intro f j z
  simp only [partialQ_derivWord, partialEta_derivWord]
  have hS : wordsOfLength (j + 1) =
      (wordsOfLength j).image (List.cons true) ∪ (wordsOfLength j).image (List.cons false) := by
    ext w
    constructor
    · intro hw
      rw [vjl_mem_wordsOfLength] at hw
      cases w with
      | nil => simp at hw
      | cons b u =>
        have hu : u.length = j := by simpa using hw
        rw [Finset.mem_union]
        cases b
        · right; exact Finset.mem_image.2 ⟨u, vjl_mem_wordsOfLength.2 hu, rfl⟩
        · left; exact Finset.mem_image.2 ⟨u, vjl_mem_wordsOfLength.2 hu, rfl⟩
    · intro hw
      rw [Finset.mem_union] at hw
      rw [vjl_mem_wordsOfLength]
      rcases hw with h | h
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
        rw [vjl_mem_wordsOfLength] at hu
        simp [hu]
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
        rw [vjl_mem_wordsOfLength] at hu
        simp [hu]
  have hdisj : Disjoint ((wordsOfLength j).image (List.cons true))
      ((wordsOfLength j).image (List.cons false)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨u', _, h⟩ := Finset.mem_image.1 h2
    simp at h
  unfold wordSq
  rw [hS, Finset.sum_union hdisj,
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h), ← Finset.sum_add_distrib]

end UnforcedLeray.Short.PartI
