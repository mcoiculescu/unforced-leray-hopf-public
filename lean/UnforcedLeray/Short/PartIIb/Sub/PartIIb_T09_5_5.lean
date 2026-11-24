import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5
import UnforcedLeray.Lib.Axisymmetric.Laplacian
import UnforcedLeray.Lib.AxisymmetricB.Lift

/-!
# Part II-b, task `PartII-b:T09/5/5` (`LapPtwise`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1639-1668 and
1912-1916 (`∂_ρ(√s b) = s Q_ε b`, `∂_z(√s b) = s ∂_η b`, hoop term `-ε² s b_r`).

`LapPtwise` splits into: the axis (`LapAxis`), the real/imaginary splitting of the Cartesian
Laplacian of `NvC` (`LapSplit`), the real chart computation `Δ (Nv R b) = Nv R (lapReal ε b)`
(`LapNvReal`) and the commutation of `reM/imM` with `classQ/classEta` (`LapCommRe`).
Proved here: `lapPtwise_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- The hoop term on a real meridional vector: `(v_r, 0)`. -/
def hoopRv (v : UnforcedLeray.Axi.Merid) : UnforcedLeray.Axi.Merid :=
  EuclideanSpace.single 0 (v 0)

/-- `Q_ε b = Σ_j (vQ ε)_j ∂_j b + dQ ε · b` for a profile with values in any real normed space. -/
def classQg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ε : ℝ) (b : Coord → E) :
    Coord → E := fun x =>
  (∑ j : Fin 3, vQ ε x j • fderiv ℝ b x (cdir j)) + dQ ε x • b x

/-- `∂_η b` for a profile with values in any real normed space. -/
def classEtaG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Coord → E) :
    Coord → E := fun x => fderiv ℝ b x (cdir 2)

/-- Real form of `lapProf / ν`: `s [ (Q_ε² + ∂_η²) b - ε² E b ]` (SP 1651-1653). -/
def lapReal (ε : ℝ) (b : Coord → UnforcedLeray.Axi.Merid) : Coord → UnforcedLeray.Axi.Merid :=
  fun x => x.1 • (classQg ε (classQg ε b) x + classEtaG (classEtaG b) x - ε ^ 2 • hoopRv (b x))

/-- **Leaf `T09/5/5/1`** (axis; SP 1912-1916): on the axis both sides vanish.  `NiceProf` gives
`b x = 0` for `x.1 < s₀` and for `x.1 > s₁`; at an axis point `age = R²/0 = 0`, so the RHS
`√age • ... = 0`; near the axis `ϱ` is small, `age > s₁`, so `NvC R b` vanishes on a neighbourhood of
the axis and its Laplacian vanishes there. -/
def LapAxis : Prop :=
  ∀ (c ε ν : ℝ) (b : CProf), 0 < c → 0 < ε → NiceProf c b →
    ∀ (t : ℝ) (y : Space), y ∈ UnforcedLeray.Axi.axis →
      nuLapT ν (NvC ε⁻¹ b) (t, y) =
        NvC ε⁻¹ (lapProf ν ε b (classQ ε (classQ ε b)) (classEta (classEta b))) (t, y)

/-- **Leaf `T09/5/5/2`** (splitting into real and imaginary parts, off the axis): `NvC` is
`realC (Nv · (reM ∘ b)) + I • realC (Nv · (imM ∘ b))`; off the axis `Nv R b t` is smooth for
smooth `b` (`chart` smooth, `frameL` smooth, `√age` smooth), `realC` is `ℝ`-linear, and `lapT` at
`(t, y)` is the vector Laplacian of the slice `z ↦ ·(t, z)`. -/
def LapSplit : Prop :=
  ∀ (R : ℝ) (b : CProf), 0 < R → ContDiff ℝ ∞ b →
    ∀ (t : ℝ) (y : Space), y ∉ UnforcedLeray.Axi.axis →
      lapT (NvC R b) (t, y) =
        realC (UnforcedLeray.Axi.vecLap
          (fun z => UnforcedLeray.Axi.Nv R (fun x => reM (b x)) t z) y) +
        Complex.I • realC (UnforcedLeray.Axi.vecLap
          (fun z => UnforcedLeray.Axi.Nv R (fun x => imM (b x)) t z) y)

/-- **Leaf `T09/5/5/3`** (the real chart computation, SP 1651-1653, 1912-1916; size L, may be
decomposed: `Nv R b t = liftMer (mp R t b)` on `axisᶜ` with the meridional profile
`mp R t b (ρ,z) = √(R²/ρ²) • b (chart)`, then `Axi.vecLap_liftMer`, then
`vecLapMer (mp R t b) = mp R t (lapReal ε b)` on `ρ > 0` from `radial_chain`, `axial_chain`
(`Lib/Axisymmetric/RingChart.lean`): `∂_ρ(√s F∘chart) = s (Q_ε F)∘chart`,
`Q_ε(√s h) = √s (Q_ε - ε) h`, `∂_z(√s F∘chart) = s (∂_η F)∘chart`, `ρ⁻¹ = ε√s`). -/
def LapNvReal : Prop :=
  ∀ (R : ℝ) (b : Coord → UnforcedLeray.Axi.Merid), 0 < R → ContDiff ℝ ∞ b →
    ∀ (t : ℝ) (y : Space), y ∉ UnforcedLeray.Axi.axis →
      UnforcedLeray.Axi.vecLap (fun z => UnforcedLeray.Axi.Nv R b t z) y =
        UnforcedLeray.Axi.Nv R (lapReal R⁻¹ b) t y

/-- **Leaf `T09/5/5/4`** (`reM`, `imM` are real-linear coordinate projections, so commute with
`fderiv`): for a smooth complex profile, `reM ∘ b`, `imM ∘ b`, `classQ ε b`, `classEta b` are smooth
and `reM (classQ ε b x) = classQg ε (reM ∘ b) x` (likewise `imM`, `classEta`). -/
def LapCommRe : Prop :=
  ∀ (ε : ℝ) (b : CProf), ContDiff ℝ ∞ b →
    ContDiff ℝ ∞ (fun x => reM (b x)) ∧ ContDiff ℝ ∞ (fun x => imM (b x)) ∧
    ContDiff ℝ ∞ (classQ ε b) ∧ ContDiff ℝ ∞ (classEta b) ∧
    (∀ x, reM (classQ ε b x) = classQg ε (fun x => reM (b x)) x) ∧
    (∀ x, imM (classQ ε b x) = classQg ε (fun x => imM (b x)) x) ∧
    (∀ x, reM (classEta b x) = classEtaG (fun x => reM (b x)) x) ∧
    (∀ x, imM (classEta b x) = classEtaG (fun x => imM (b x)) x)

theorem reM_real_smul (r : ℝ) (v : CMerid) : reM (((r : ℝ) : ℂ) • v) = r • reM v := by
  ext i; simp [reM]

theorem imM_real_smul (r : ℝ) (v : CMerid) : imM (((r : ℝ) : ℂ) • v) = r • imM v := by
  ext i; simp [imM]

theorem reM_add (u v : CMerid) : reM (u + v) = reM u + reM v := by
  ext i; simp [reM]

theorem imM_add (u v : CMerid) : imM (u + v) = imM u + imM v := by
  ext i; simp [imM]

theorem reM_sub (u v : CMerid) : reM (u - v) = reM u - reM v := by
  ext i; simp [reM]

theorem imM_sub (u v : CMerid) : imM (u - v) = imM u - imM v := by
  ext i; simp [imM]

theorem reM_hoopE (v : CMerid) : reM (hoopE v) = hoopRv (reM v) := by
  ext i; fin_cases i <;> simp [reM, hoopE, hoopRv]

theorem imM_hoopE (v : CMerid) : imM (hoopE v) = hoopRv (imM v) := by
  ext i; fin_cases i <;> simp [imM, hoopE, hoopRv]

theorem realC_real_smul (r : ℝ) (x : Space) : realC (r • x) = ((r : ℝ) : ℂ) • realC x := by
  ext i; simp [realC_apply]

theorem lapProf_re (ν ε : ℝ) (b Q2b E2b : CProf) :
    (fun x => reM (lapProf ν ε b Q2b E2b x)) = fun x =>
      (ν • (x.1 • (reM (Q2b x) + reM (E2b x) - ε ^ 2 • hoopRv (reM (b x))))) := by
  funext x
  simp only [lapProf]
  rw [reM_real_smul, reM_sub, reM_add, reM_real_smul, reM_hoopE, mul_smul]

theorem lapProf_im (ν ε : ℝ) (b Q2b E2b : CProf) :
    (fun x => imM (lapProf ν ε b Q2b E2b x)) = fun x =>
      (ν • (x.1 • (imM (Q2b x) + imM (E2b x) - ε ^ 2 • hoopRv (imM (b x))))) := by
  funext x
  simp only [lapProf]
  rw [imM_real_smul, imM_sub, imM_add, imM_real_smul, imM_hoopE, mul_smul]

theorem lapPtwise_of (h1 : LapAxis) (h2 : LapSplit) (h3 : LapNvReal) (h4 : LapCommRe) :
    LapPtwise := by
  intro c ε ν b hc hε hb t y
  by_cases hy : y ∈ UnforcedLeray.Axi.axis
  · exact h1 c ε ν b hc hε hb t y hy
  have hbS : ContDiff ℝ ∞ b := hb.1
  have hR0 : 0 < ε⁻¹ := inv_pos.2 hε
  obtain ⟨hre, him, hQs, hEs, hQre, hQim, hEre, hEim⟩ := h4 ε b hbS
  obtain ⟨-, -, -, -, hQre2, hQim2, -, -⟩ := h4 ε (classQ ε b) hQs
  obtain ⟨-, -, -, -, -, -, hEre2, hEim2⟩ := h4 ε (classEta b) hEs
  have eQre : (fun x => reM (classQ ε b x)) = classQg ε (fun x => reM (b x)) := funext hQre
  have eQim : (fun x => imM (classQ ε b x)) = classQg ε (fun x => imM (b x)) := funext hQim
  have eEre : (fun x => reM (classEta b x)) = classEtaG (fun x => reM (b x)) := funext hEre
  have eEim : (fun x => imM (classEta b x)) = classEtaG (fun x => imM (b x)) := funext hEim
  have kre : (fun x => reM (lapProf ν ε b (classQ ε (classQ ε b)) (classEta (classEta b)) x)) =
      ν • lapReal ε (fun x => reM (b x)) := by
    rw [lapProf_re]
    funext x
    simp only [lapReal, Pi.smul_apply]
    rw [hQre2 x, hEre2 x, eQre, eEre]
  have kim : (fun x => imM (lapProf ν ε b (classQ ε (classQ ε b)) (classEta (classEta b)) x)) =
      ν • lapReal ε (fun x => imM (b x)) := by
    rw [lapProf_im]
    funext x
    simp only [lapReal, Pi.smul_apply]
    rw [hQim2 x, hEim2 x, eQim, eEim]
  have hL : nuLapT ν (NvC ε⁻¹ b) (t, y) = ν • lapT (NvC ε⁻¹ b) (t, y) := rfl
  rw [hL, h2 ε⁻¹ b hR0 hbS t y hy, h3 ε⁻¹ _ hR0 hre t y hy, h3 ε⁻¹ _ hR0 him t y hy]
  simp only [NvC]
  rw [kre, kim, inv_inv, UnforcedLeray.Axi.Nv_smul, UnforcedLeray.Axi.Nv_smul, realC_real_smul,
    realC_real_smul]
  rw [smul_add, smul_comm (ν : ℝ) Complex.I]
  simp only [Complex.coe_smul]

end UnforcedLeray.Short.IIb
