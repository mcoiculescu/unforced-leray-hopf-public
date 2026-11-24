import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticAInt.Helpers

/-!


Source: `the November 2 reference manuscript` lines 285-287. For a word `w` of
length `j`, the gradient energy `∑_k |∇ ∂_w f_k|²` and the squared curl `(∂_w curl f)²` are
integrable on the cell. Each integrand is dominated by a constant times `‖D^m f‖²` with
`m ∈ {j, j+1}` (word derivatives of length `m` are bounded by the `m`-th jet), and the jets are
square integrable on the cell by `APEllipticData`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open APEllipticHelp

theorem apEllipticAInt : APEllipticAInt := by
  intro j c f hf w _hw
  refine ⟨?_, ?_⟩
  · have hq : ∀ k : Fin 2, IntegrableOn (fun z => Cyl.partialQ (wordComp w f k) z ^ 2 +
        Cyl.partialEta (wordComp w f k) z ^ 2) (Cyl.cell c) := by
      intro k
      have e1 : Cyl.partialQ (wordComp w f k) = B0151.derivWord (true :: w) (vcomp f k) :=
        rq_word (vcomp_smooth (apData_smooth hf) k) w
      have e2 : Cyl.partialEta (wordComp w f k) = B0151.derivWord (false :: w) (vcomp f k) :=
        re_word (vcomp_smooth (apData_smooth hf) k) w
      rw [e1, e2]
      exact Integrable.add (integrableOn_sq_word hf k (true :: w))
        (integrableOn_sq_word hf k (false :: w))
    simp only [Fin.sum_univ_two]
    exact Integrable.add (hq 0) (hq 1)
  · have e : (fun z => B0151.derivWord w (Cyl.curl f) z ^ 2) =
        fun z => (B0151.derivWord (true :: w) (vcomp f 1) z
          - B0151.derivWord (false :: w) (vcomp f 0) z) ^ 2 := by
      funext z
      rw [curl_word_eq (apData_smooth hf) w z]
    rw [e]
    exact integrableOn_curl_sq hf w

end UnforcedLeray.Short.PartI
