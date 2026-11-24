import UnforcedLeray.Loc.L12Equivariance.Fields
import UnforcedLeray.Loc.L03Evolution.Free
import UnforcedLeray.Loc.L03Evolution.Abstract
import UnforcedLeray.Infra.VolterraEvolution

/-!
# L12 helper: `𝒪` commutes with `S₀`, `𝓑_*` and the evolution `E(τ,s)`

`paper/main.tex` lines 563–566 (step L12, blueprint unit B1025): "By hypothesis `u_dss`,
`U_*` and `b_*` are `𝒪`-invariant. The action commutes with `𝒜_h`, `𝔓` and the
Navier–Stokes nonlinearity, hence with `𝓑_*`, its evolution, …". Here, for `g ∈ 𝒪`:

* `S₀(s) (g·f) = g·S₀(s) f` on `X` (`s ≥ 0`) and `L²_div → X` (`s > 0`), from the literal
  formula `IsFreeEvolution.rep`, `repL` and `freeEvolution_rotateField`;
* `𝓑_*(τ)(g·f) = g·𝓑_*(τ) f` (`B_rotX`), from the weak characterization
  `IsCoefficients.B_weak`, the invariance of `U_*(τ)` (`IsExactBackground.Ustar_symmetric`),
  `IsMinusLerayDiv.rot` and uniqueness of the weak `-𝔓 div`;
* `E(τ,s)` commutes with any bounded `A` that commutes with `S₀`, `S₀ : L²_div → X` and `𝓑_*`
  (`E_comm_of`): `A E(·,s) f - E(·,s) A f` solves the homogeneous Volterra equation of
  line 299 on each unit strip, so it vanishes by `VolterraData.eq_zero_of_homogeneous`

  law extends this to all `s ≤ τ`. The Volterra data are those of

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Blueprint.L12

open SobolevGraph
open UnforcedLeray.Infra.VolterraEvolution
open UnforcedLeray.Loc.L03Evolution (free_bounds continuousOn_S0L exists_norm_le_of_periodic)

variable (g : Space ≃ₗᵢ[ℝ] Space)

/-! ## The free evolution and the coefficients -/

theorem S0_rotX {h : ℝ} {S : FreeEvolution} (hS : IsFreeEvolution h S) {s : ℝ} (hs : 0 ≤ s)
    (f : X) : S.S0 s (rotX g f) = rotX g (S.S0 s f) := by
  apply L10.Xclass_injective
  apply Lp.ext
  have h1 := hS.rep s hs (rotX g f)
  have h2 := UnforcedLeray.B0418.freeEvolution_congr_ae (Xval_rotX g f) h s
  have h3 := rotateField_congr g (hS.rep s hs f)
  have h4 := Xval_rotX g (S.S0 s f)
  refine h1.trans (h2.trans ?_)
  rw [freeEvolution_rotateField]
  exact (h4.trans h3).symm

theorem S0L_rotL {h : ℝ} {S : FreeEvolution} (hS : IsFreeEvolution h S) {s : ℝ} (hs : 0 < s)
    (F : L2div) : S.S0L s (rotL g F) = rotX g (S.S0L s F) := by
  apply L10.Xclass_injective
  apply Lp.ext
  have h1 := hS.repL s hs (rotL g F)
  have h2 := UnforcedLeray.B0418.freeEvolution_congr_ae (Lval_rotL g F) h s
  have h3 := rotateField_congr g (hS.repL s hs F)
  have h4 := Xval_rotX g (S.S0L s F)
  refine h1.trans (h2.trans ?_)
  rw [freeEvolution_rotateField]
  exact (h4.trans h3).symm

/-- `𝓑_*(τ)(g·f) = g·𝓑_*(τ) f` for `g ∈ 𝒪`. -/
theorem B_rotX {D : BackgroundData} (hD : IsUnstableBackground D) {c : Coefficients}
    (hc : IsCoefficients D c) {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (r : ℝ) (f : X) :
    c.B r (rotX g f) = rotL g (c.B r f) := by
  apply Lclass_injective
  rw [Lclass_rotL]
  refine L10.IsMinusLerayDiv.unique (hc.B_weak r (rotX g f)) ?_
  have h := IsMinusLerayDiv.rot g (hc.B_weak r f)
  rw [← symTensorColumns_rot] at h
  have hU : rotateField g (D.Ustar r) =ᵐ[volume] D.Ustar r := hD.1.Ustar_symmetric r g hg
  exact L10.IsMinusLerayDiv.congr h
    (fun j => symTensorColumns_congr hU (Xval_rotX g f).symm j)

/-! ## The evolution -/

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}

/-- Any bounded operator commuting with `S₀`, `S₀ : L²_div → X` and `𝓑_*` commutes with the
evolution `E(τ,s)` (lines 299–300: `E` is the unique solution of its Volterra equation). -/
theorem E_comm_of (hD : IsUnstableBackground D) (hc : IsCoefficients D c)
    (hS : IsFreeEvolution D.h S) (hev : IsEvolution D c S ev)
    (A : X →L[ℝ] X) (AL : L2div →L[ℝ] L2div)
    (hS0 : ∀ s, 0 ≤ s → ∀ f, S.S0 s (A f) = A (S.S0 s f))
    (hS0L : ∀ s, 0 < s → ∀ F, S.S0L s (AL F) = A (S.S0L s F))
    (hB : ∀ r f, c.B r (A f) = AL (c.B r f)) :
    ∀ s τ, s ≤ τ → ∀ f, ev.E τ s (A f) = A (ev.E τ s f) := by
  have hh : 0 < D.h := hD.1.h_pos
  have hP : 0 < D.period := hD.1.period_pos
  obtain ⟨C, -, hC0, hC0L, -⟩ := free_bounds hS
  obtain ⟨β, hβ⟩ := exists_norm_le_of_periodic hP.ne' hc.B_periodic hc.B_continuous
  let V : VolterraData ℝ X L2div :=
    { S₀ := S.S0
      S := S.S0L
      B := c.B
      M₀ := C
      C₀ := C
      β := β
      norm_S₀_le := fun t ht _ => hC0 t ht
      norm_S_le := hC0L
      norm_B_le := hβ
      continuousOn_S₀ := fun x => (hS.strongly_continuous x).mono Icc_subset_Ici_self
      continuousOn_S := fun y => (continuousOn_S0L hS hh.le y).mono fun t ht => ht.1
      continuous_B := fun x => hc.B_continuous.clm_apply continuous_const }
  -- the unit strip
  have short : ∀ s τ, s ≤ τ → τ ≤ s + 1 → ∀ f, ev.E τ s (A f) = A (ev.E τ s f) := by
    intro s τ₁ hsτ₁ hτ₁ f
    let w : ℝ → X := fun τ => A (ev.E τ s f) - ev.E τ s (A f)
    have hcont : ∀ y : X, ContinuousOn (fun τ => ev.E τ s y) (Icc s (s + 1)) := by
      intro y
      exact (hev.strongly_continuous y).comp
        (continuous_id.prodMk continuous_const).continuousOn (fun τ hτ => hτ.1)
    have hw : ContinuousOn w (Icc s (s + 1)) :=
      (A.continuous.comp_continuousOn (hcont f)).sub (hcont (A f))
    have heq : ∀ τ ∈ Icc s (s + 1), w τ = V.vol s w τ := by
      intro τ hτ
      have hsτ : s ≤ τ := hτ.1
      have i1 := hev.duhamel_integrable s τ hsτ f
      have i2 := hev.duhamel_integrable s τ hsτ (A f)
      have i3 : IntegrableOn (fun r => S.S0L (τ - r) (c.B r (A (ev.E r s f)))) (Ioo s τ) := by
        refine (A.integrable_comp i1).congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        rw [hB, hS0L (τ - r) (by linarith [hr.2])]
      have e1 : A (∫ r in Ioo s τ, S.S0L (τ - r) (c.B r (ev.E r s f))) =
          ∫ r in Ioo s τ, S.S0L (τ - r) (c.B r (A (ev.E r s f))) := by
        rw [← A.integral_comp_comm i1]
        refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
        rw [hB, hS0L (τ - r) (by linarith [hr.2])]
      have e2 : V.vol s w τ = ∫ r in Ioo s τ, S.S0L (τ - r) (c.B r (w r)) := by
        show (∫ r in s..τ, S.S0L (τ - r) (c.B r (w r))) = _
        rw [intervalIntegral.integral_of_le hsτ, integral_Ioc_eq_integral_Ioo]
      rw [e2]
      show A (ev.E τ s f) - ev.E τ s (A f) = _
      rw [hev.duhamel s τ hsτ f, hev.duhamel s τ hsτ (A f), map_add, e1, hS0 (τ - s)
        (by linarith) f, add_sub_add_left_eq_sub, ← integral_sub i3 i2]
      refine setIntegral_congr_fun measurableSet_Ioo (fun r _ => ?_)
      simp only [w, map_sub]
    exact (sub_eq_zero.mp (V.eq_zero_of_homogeneous le_rfl hw heq τ₁ ⟨hsτ₁, hτ₁⟩)).symm
  -- all strips, by the evolution law
  have hn : ∀ n : ℕ, ∀ s τ : ℝ, s ≤ τ → τ ≤ s + (n : ℝ) → ∀ f,
      ev.E τ s (A f) = A (ev.E τ s f) := by
    intro n
    induction n with
    | zero =>
      intro s τ hsτ hτ f
      have : τ = s := le_antisymm (by simpa using hτ) hsτ
      subst this
      rw [hev.at_diag]
      rfl
    | succ n ih =>
      intro s τ hsτ hτ f
      by_cases h1 : τ ≤ s + 1
      · exact short s τ hsτ h1 f
      · push Not at h1
        have hlaw : ∀ y, ev.E τ s y = ev.E τ (s + 1) (ev.E (s + 1) s y) := by
          intro y
          rw [← hev.law s (s + 1) τ (by linarith) h1.le]
          rfl
        rw [hlaw, hlaw, short s (s + 1) (by linarith) le_rfl f,
          ih (s + 1) τ h1.le (by push_cast at hτ; linarith)]
  intro s τ hsτ f
  exact hn ⌈τ - s⌉₊ s τ hsτ (by linarith [Nat.le_ceil (τ - s)]) f

/-- `E(τ,s)` commutes with `g ∈ 𝒪` on `X`. -/
theorem E_rotX (hD : IsUnstableBackground D) (hc : IsCoefficients D c)
    (hS : IsFreeEvolution D.h S) (hev : IsEvolution D c S ev) {g : Space ≃ₗᵢ[ℝ] Space}
    (hg : FixesAxis g) : ∀ s τ, s ≤ τ → ∀ f, ev.E τ s (rotX g f) = rotX g (ev.E τ s f) :=
  E_comm_of hD hc hS hev (rotX g) (rotL g) (fun _ hs f => S0_rotX g hS hs f)
    (fun _ hs F => S0L_rotL g hS hs F) (fun r f => B_rotX hD hc hg r f)

end UnforcedLeray.Blueprint.L12
