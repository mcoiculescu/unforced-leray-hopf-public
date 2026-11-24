import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Words commute with sums (on `tjU`). -/
theorem tjW_add_aux (f g : ℝ × (ℝ × ℝ) → ℝ) (hf : ContDiffOn ℝ ∞ f tjU)
    (hg : ContDiffOn ℝ ∞ g tjU) :
    ∀ L : List (Fin 3), ∀ p ∈ tjU, tjW L (fun q => f q + g q) p = tjW L f p + tjW L g p := by
  intro L
  induction L with
  | nil =>
    intro p _
    rfl
  | cons a L ih =>
    intro p hp
    have e : fderivWithin ℝ (tjW L (fun q => f q + g q)) tjU p =
        fderivWithin ℝ (fun q => tjW L f q + tjW L g q) tjU p :=
      fderivWithin_congr (fun q hq => ih q hq) (ih p hp)
    have hdf : DifferentiableWithinAt ℝ (tjW L f) tjU p :=
      ((tjW_contDiffOn hf L).differentiableOn (by simp)) p hp
    have hdg : DifferentiableWithinAt ℝ (tjW L g) tjU p :=
      ((tjW_contDiffOn hg L).differentiableOn (by simp)) p hp
    have h2 : fderivWithin ℝ (fun q => tjW L f q + tjW L g q) tjU p =
        fderivWithin ℝ (tjW L f) tjU p + fderivWithin ℝ (tjW L g) tjU p :=
      fderivWithin_add (uniqueDiffOn_tjU p hp) hdf hdg
    simp only [tjW_cons]
    rw [e, h2, add_apply]

/-- Words commute with differences (on `tjU`). -/
theorem tjW_sub_aux (f g : ℝ × (ℝ × ℝ) → ℝ) (hf : ContDiffOn ℝ ∞ f tjU)
    (hg : ContDiffOn ℝ ∞ g tjU) :
    ∀ L : List (Fin 3), ∀ p ∈ tjU, tjW L (fun q => f q - g q) p = tjW L f p - tjW L g p := by
  intro L
  induction L with
  | nil =>
    intro p _
    rfl
  | cons a L ih =>
    intro p hp
    have e : fderivWithin ℝ (tjW L (fun q => f q - g q)) tjU p =
        fderivWithin ℝ (fun q => tjW L f q - tjW L g q) tjU p :=
      fderivWithin_congr (fun q hq => ih q hq) (ih p hp)
    have hdf : DifferentiableWithinAt ℝ (tjW L f) tjU p :=
      ((tjW_contDiffOn hf L).differentiableOn (by simp)) p hp
    have hdg : DifferentiableWithinAt ℝ (tjW L g) tjU p :=
      ((tjW_contDiffOn hg L).differentiableOn (by simp)) p hp
    have h2 : fderivWithin ℝ (fun q => tjW L f q - tjW L g q) tjU p =
        fderivWithin ℝ (tjW L f) tjU p - fderivWithin ℝ (tjW L g) tjU p :=
      fderivWithin_sub (uniqueDiffOn_tjU p hp) hdf hdg
    simp only [tjW_cons]
    rw [e, h2, sub_apply]

/-- Words commute with constant multiples (on `tjU`). -/
theorem tjW_smul_aux (r : ℝ) (f : ℝ × (ℝ × ℝ) → ℝ) (hf : ContDiffOn ℝ ∞ f tjU) :
    ∀ L : List (Fin 3), ∀ p ∈ tjU, tjW L (fun q => r * f q) p = r * tjW L f p := by
  intro L
  induction L with
  | nil =>
    intro p _
    rfl
  | cons a L ih =>
    intro p hp
    have e : fderivWithin ℝ (tjW L (fun q => r * f q)) tjU p =
        fderivWithin ℝ (fun q => r * tjW L f q) tjU p :=
      fderivWithin_congr (fun q hq => ih q hq) (ih p hp)
    have hdf : DifferentiableWithinAt ℝ (tjW L f) tjU p :=
      ((tjW_contDiffOn hf L).differentiableOn (by simp)) p hp
    simp only [tjW_cons]
    rw [e, fderivWithin_const_mul (uniqueDiffOn_tjU p hp) hdf r,
      smul_apply, smul_eq_mul]

/-- Words commute with composition by a continuous linear functional (on `tjU`). -/
theorem tjW_clm_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : E →L[ℝ] ℝ)
    (h : ℝ × (ℝ × ℝ) → E) (hh : ContDiffOn ℝ ∞ h tjU) :
    ∀ L : List (Fin 3), ∀ p ∈ tjU, tjW L (fun q => ℓ (h q)) p = ℓ (tjW L h p) := by
  intro L
  induction L with
  | nil =>
    intro p _
    rfl
  | cons a L ih =>
    intro p hp
    have e : fderivWithin ℝ (tjW L (fun q => ℓ (h q))) tjU p =
        fderivWithin ℝ (fun q => ℓ (tjW L h q)) tjU p :=
      fderivWithin_congr (fun q hq => ih q hq) (ih p hp)
    have hdiff : DifferentiableWithinAt ℝ (tjW L h) tjU p :=
      ((tjW_contDiffOn hh L).differentiableOn (by simp)) p hp
    have hd2 : HasFDerivWithinAt (fun q => ℓ (tjW L h q)) (ℓ.comp (fderivWithin ℝ (tjW L h) tjU p))
        tjU p :=
      (ℓ.hasFDerivAt (x := tjW L h p)).comp_hasFDerivWithinAt p hdiff.hasFDerivWithinAt
    have h3 : fderivWithin ℝ (fun q => ℓ (tjW L h q)) tjU p =
        ℓ.comp (fderivWithin ℝ (tjW L h) tjU p) :=
      hd2.fderivWithin (uniqueDiffOn_tjU p hp)
    simp only [tjW_cons]
    rw [e, h3, ContinuousLinearMap.comp_apply]

/-- **Words are linear and commute with components** (calculus): on `tjU`, for fields `C^∞` on
`tjU`, `tjW L (f + g) = tjW L f + tjW L g`, `tjW L (f - g) = tjW L f - tjW L g`,
`tjW L (r f) = r tjW L f`, and `tjW L (h · j) = (tjW L h) j` for a vector field `h`. (Induction on
`L` with `fderivWithin_add`, `fderivWithin_sub`, `fderivWithin_const_mul`, and
`(EuclideanSpace.proj j).fderivWithin_comp` / `fderivWithin_clm_apply`; `tjW_congr` on `tjU`.) -/
theorem tjWLinear : TjWLinear := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f g hf hg L p hp
    exact tjW_add_aux f g hf hg L p hp
  · intro f g hf hg L p hp
    exact tjW_sub_aux f g hf hg L p hp
  · intro r f hf L p hp
    exact tjW_smul_aux r f hf L p hp
  · intro h hh j L p hp
    exact tjW_clm_aux (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) h hh L p hp

end UnforcedLeray.Short.IIIa
