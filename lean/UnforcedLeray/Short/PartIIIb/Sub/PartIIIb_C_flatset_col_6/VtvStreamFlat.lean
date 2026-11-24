import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6

/-!
# `∇^⊥ζ` is a flat test (source 3511-3514)

Smoothness, periodicity, uniform support from the stream-test band, and `div ∇^⊥ζ = 0` from
symmetry of second derivatives of the smooth `ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest)

private theorem pd_eq_fderiv (ζ : ℝ → ℝ × ℝ → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2))
    (j : Fin 2) (s : ℝ) (x : ℝ × ℝ) :
    B0579.pd j (ζ s) x =
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) (s, x) (0, B0579.dir j) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) (s, x) :=
    (hF.differentiable (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => (s, y)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_prodMk_right s x
  have h2 := hd.hasFDerivAt.comp x h1
  have h3 : (ζ s) = (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) ∘ (fun y : ℝ × ℝ => (s, y)) := rfl
  unfold B0579.pd
  rw [h3, h2.fderiv]
  rfl

private theorem pd_contDiff (ζ : ℝ → ℝ × ℝ → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2))
    (j : Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (ζ p.1) p.2) := by
  have : (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (ζ p.1) p.2) =
      fun p => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) p (0, B0579.dir j) := by
    funext p; exact pd_eq_fderiv ζ hF j p.1 p.2
  rw [this]
  exact (hF.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

private theorem pd_zero (ζ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) (j : Fin 2)
    (h : ζ s =ᶠ[𝓝 x] fun _ => 0) : B0579.pd j (ζ s) x = 0 := by
  unfold B0579.pd
  rw [h.fderiv_eq]
  simp

private theorem pd_symm (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (x : ℝ × ℝ) :
    B0579.pd 0 (B0579.pd 1 f) x = B0579.pd 1 (B0579.pd 0 f) x := by
  have hs : IsSymmSndFDerivAt ℝ f x :=
    (hf.contDiffAt).isSymmSndFDerivAt (by simp)
  have hdf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  have key : ∀ j : Fin 2, ∀ k : Fin 2,
      B0579.pd k (B0579.pd j f) x = fderiv ℝ (fderiv ℝ f) x (B0579.dir k) (B0579.dir j) := by
    intro j k
    unfold B0579.pd
    have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hdf.differentiable (by simp)).differentiableAt
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key]
  exact hs _ _

theorem vtvStreamFlat : VtvStreamFlat := by
  intro c ζ hζ
  obtain ⟨hF, hcyl, s₁, s₂, R, hs₁, hsupp⟩ := hζ
  have hpd : ∀ j s, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B0579.pd j (ζ s)) := fun j s =>
    ((hcyl s).pd j).smooth
  refine ⟨?_, ?_, ⟨s₁, s₂, R, hs₁, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · simpa [streamField] using (pd_contDiff ζ hF 1).neg
    · simpa [streamField] using pd_contDiff ζ hF 0
  · intro s x i
    fin_cases i
    · simp [streamField, ((hcyl s).pd 1).periodic x]
    · simp [streamField, ((hcyl s).pd 0).periodic x]
  · intro s x i h
    have hev : ζ s =ᶠ[𝓝 x] fun _ => 0 := by
      rcases h with h | h | h
      · have : ζ s = fun _ => 0 := funext fun y => hsupp s y (Or.inl h)
        rw [this]
      · have : ζ s = fun _ => 0 := funext fun y => hsupp s y (Or.inr (Or.inl h))
        rw [this]
      · have hopen : IsOpen {y : ℝ × ℝ | R < |y.2|} :=
          isOpen_lt continuous_const (continuous_snd.abs)
        filter_upwards [hopen.mem_nhds h] with y hy
        exact hsupp s y (Or.inr (Or.inr hy))
    fin_cases i
    · simp [streamField, pd_zero ζ s x 1 hev]
    · simp [streamField, pd_zero ζ s x 0 hev]
  · intro s x
    have hs := pd_symm (ζ s) (hcyl s).smooth x
    have hneg : B0579.pd 0 (fun y => streamField ζ s y 0) x = - B0579.pd 0 (B0579.pd 1 (ζ s)) x := by
      have : (fun y => streamField ζ s y 0) = fun y => -(B0579.pd 1 (ζ s) y) := by
        funext y; simp [streamField]
      rw [this]
      unfold B0579.pd
      rw [fderiv_fun_neg]
      simp
    have h1 : (fun y => streamField ζ s y 1) = B0579.pd 0 (ζ s) := by
      funext y; simp [streamField]
    rw [hneg, h1, hs]
    ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
