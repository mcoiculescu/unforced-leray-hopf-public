import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5_5
import UnforcedLeray.Lib.AxisymmetricB.Range
import UnforcedLeray.Units.B0186

/-!
# Part II-b, task `PartII-b:T09/5/5/3` (`LapNvReal`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.
`Nv R b t = liftMer (mp R t b)` with the meridional profile
`mp R t b (ρ,z) = √(R²/ρ²) • b (merChart R t (ρ,z))`; then `Axi.vecLap_liftMer`, and the identity
`vecLapMer (mp R t b) = mp R t (lapReal R⁻¹ b)` on `ρ > 0`, which follows from the four first-order
chain-rule leaves below.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Axi

/-- The meridional profile of the ring lift. -/
def mp (R τ : ℝ) (F : Coord → Merid) : ℝ × ℝ → Merid :=
  fun q => √(R ^ 2 / q.1 ^ 2) • F (merChart R τ q)

/-- The open half plane `{ρ > 0}` in meridional coordinates, and the same in chart coordinates. -/
abbrev halfM : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ

abbrev halfC : Set Coord := Ioi 0 ×ˢ univ

/-- **Leaf `/1`** (smoothness; SP 1639-1668). For `F` smooth on `{s > 0}` and `R > 0`, `mp R τ F` is
`C²` on `{ρ > 0}` (`merChart` is smooth there and maps into `{s > 0}`; `√(R²/ρ²) = R/ρ`). -/
def MpSmooth : Prop :=
  ∀ (R τ : ℝ) (F : Coord → Merid), 0 < R → ContDiffOn ℝ ∞ F halfC →
    ContDiffOn ℝ 2 (mp R τ F) halfM

/-- **Leaf `/2`** (radial chain rule; SP 1651-1653, `Axi.radial_chain`). For `ρ > 0`,
`∂_ρ(√s F∘chart) = s (Q_ε F)∘chart`, `ε = R⁻¹`, i.e. `dρ (mp R τ F) = mp R τ (√s • Q_ε F)`
(use `radial_chain` for the factor `F ∘ chart`, `d/dρ (R/ρ) = -(R/ρ²)`). -/
def MpDRho : Prop :=
  ∀ (R τ : ℝ) (F : Coord → Merid), 0 < R → ContDiffOn ℝ ∞ F halfC →
    ∀ p : ℝ × ℝ, 0 < p.1 →
      dρ (mp R τ F) p = mp R τ (fun x => √x.1 • classQg R⁻¹ F x) p

/-- **Leaf `/3`** (axial chain rule; `Axi.axial_chain`). For `ρ > 0`,
`dz (mp R τ F) = mp R τ (√s • ∂_η F)`. -/
def MpDZ : Prop :=
  ∀ (R τ : ℝ) (F : Coord → Merid), 0 < R → ContDiffOn ℝ ∞ F halfC →
    ∀ p : ℝ × ℝ, 0 < p.1 →
      dz (mp R τ F) p = mp R τ (fun x => √x.1 • classEtaG F x) p

/-- **Leaf `/4`**: `Q_ε (√s h) = √s (Q_ε h - ε h)` for `h` smooth on `{s > 0}` at `s > 0`
(`∂_s √s = 1/(2√s)`, `vQ ε x 0 = -2 ε s`). -/
def SqrtQ : Prop :=
  ∀ (ε : ℝ) (H : Coord → Merid) (x : Coord), 0 < x.1 → ContDiffOn ℝ ∞ H halfC →
    classQg ε (fun y => √y.1 • H y) x = √x.1 • (classQg ε H x - ε • H x)

/-- **Leaf `/5`**: `∂_η (√s h) = √s ∂_η h` at `s > 0`. -/
def SqrtEta : Prop :=
  ∀ (H : Coord → Merid) (x : Coord), 0 < x.1 → ContDiffOn ℝ ∞ H halfC →
    classEtaG (fun y => √y.1 • H y) x = √x.1 • classEtaG H x


/-! ### Reduction -/

theorem contDiffOn_halfC_sqrt_smul {H : Coord → Merid} (hH : ContDiffOn ℝ ∞ H halfC) :
    ContDiffOn ℝ ∞ (fun x => √x.1 • H x) halfC := by
  have hs : ContDiffOn ℝ ∞ (fun x : Coord => √x.1) halfC := by
    intro x hx
    have hx0 : x.1 ≠ 0 := ne_of_gt hx.1
    exact ((Real.contDiffAt_sqrt hx0).comp x contDiff_fst.contDiffAt).contDiffWithinAt
  exact hs.smul hH

theorem contDiffOn_classQg {ε : ℝ} {F : Coord → Merid} (hF : ContDiffOn ℝ ∞ F halfC) :
    ContDiffOn ℝ ∞ (classQg ε F) halfC := by
  have hd : ∀ j : Fin 3, ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x (cdir j)) halfC := fun j => by
    have := hF.fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) (m := ∞) (by simp)
    exact this.clm_apply (contDiffOn_const (c := cdir j))
  have hv : ∀ j : Fin 3, ContDiffOn ℝ ∞ (fun x => vQ ε x j) halfC := fun j => by
    apply ContDiff.contDiffOn
    fin_cases j <;> simp [vQ] <;> fun_prop
  unfold classQg
  refine ContDiffOn.add (ContDiffOn.sum fun j _ => (hv j).smul (hd j)) ?_
  exact (contDiffOn_const (c := -ε)).smul hF

theorem contDiffOn_classEtaG {F : Coord → Merid} (hF : ContDiffOn ℝ ∞ F halfC) :
    ContDiffOn ℝ ∞ (classEtaG F) halfC := by
  have := hF.fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) (m := ∞) (by simp)
  exact this.clm_apply (contDiffOn_const (c := cdir 2))


theorem isOpen_halfM : IsOpen halfM := isOpen_Ioi.prod isOpen_univ

theorem merChart_fst_pos {R τ : ℝ} (hR : 0 < R) {p : ℝ × ℝ} (hp : 0 < p.1) :
    0 < (merChart R τ p).1 := by
  show 0 < R ^ 2 / p.1 ^ 2
  positivity

theorem mp_congr {R τ : ℝ} (hR : 0 < R) {F F' : Coord → Merid}
    (h : ∀ x : Coord, 0 < x.1 → F x = F' x) {p : ℝ × ℝ} (hp : 0 < p.1) :
    mp R τ F p = mp R τ F' p := by
  simp only [mp]
  congr 1
  exact h _ (merChart_fst_pos hR hp)

theorem sqrt_s {R : ℝ} (hR : 0 < R) {p : ℝ × ℝ} (hp : 0 < p.1) : √(R ^ 2 / p.1 ^ 2) = R / p.1 := by
  rw [← div_pow, Real.sqrt_sq (by positivity)]

theorem dρ_proj {h : ℝ × ℝ → Merid} {p : ℝ × ℝ} (hd : DifferentiableAt ℝ h p) (i : Fin 2) :
    dρ (fun q => h q i) p = dρ h p i := by
  have := (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).hasFDerivAt.comp p hd.hasFDerivAt
  simp only [dρ]
  rw [show (fun q => h q i) = (EuclideanSpace.proj i : Merid →L[ℝ] ℝ) ∘ h from rfl, this.fderiv]
  rfl

theorem dz_proj {h : ℝ × ℝ → Merid} {p : ℝ × ℝ} (hd : DifferentiableAt ℝ h p) (i : Fin 2) :
    dz (fun q => h q i) p = dz h p i := by
  have := (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).hasFDerivAt.comp p hd.hasFDerivAt
  simp only [dz]
  rw [show (fun q => h q i) = (EuclideanSpace.proj i : Merid →L[ℝ] ℝ) ∘ h from rfl, this.fderiv]
  rfl

theorem lapMer_proj {b : ℝ × ℝ → Merid} (hb : ContDiffOn ℝ 2 b halfM) {p : ℝ × ℝ} (hp : 0 < p.1)
    (i : Fin 2) :
    lapMer (fun q => b q i) p = (dρ (dρ b) p + p.1⁻¹ • dρ b p + dz (dz b) p) i := by
  have hpm : p ∈ halfM := ⟨hp, trivial⟩
  have hnh : halfM ∈ 𝓝 p := isOpen_halfM.mem_nhds hpm
  have hdb : ∀ q ∈ halfM, DifferentiableAt ℝ b q := fun q hq =>
    (hb.contDiffAt (isOpen_halfM.mem_nhds hq)).differentiableAt (by norm_num)
  have hd1 : ContDiffOn ℝ 1 (fun q => fderiv ℝ b q) halfM :=
    hb.fderiv_of_isOpen isOpen_halfM (m := 1) (by norm_num)
  have hdρ : ContDiffOn ℝ 1 (dρ b) halfM := hd1.clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))
  have hdz : ContDiffOn ℝ 1 (dz b) halfM := hd1.clm_apply (contDiffOn_const (c := ((0 : ℝ), (1 : ℝ))))
  have hdρd : DifferentiableAt ℝ (dρ b) p :=
    (hdρ.contDiffAt hnh).differentiableAt (by norm_num)
  have hdzd : DifferentiableAt ℝ (dz b) p :=
    (hdz.contDiffAt hnh).differentiableAt (by norm_num)
  have e1 : (dρ fun q => b q i) =ᶠ[𝓝 p] fun q => dρ b q i := by
    filter_upwards [hnh] with q hq using dρ_proj (hdb q hq) i
  have e2 : (dz fun q => b q i) =ᶠ[𝓝 p] fun q => dz b q i := by
    filter_upwards [hnh] with q hq using dz_proj (hdb q hq) i
  have a1 : dρ (dρ fun q => b q i) p = dρ (fun q => dρ b q i) p := by
    show fderiv ℝ (dρ fun q => b q i) p (1, 0) = fderiv ℝ (fun q => dρ b q i) p (1, 0)
    rw [e1.fderiv_eq]
  have a2 : dz (dz fun q => b q i) p = dz (fun q => dz b q i) p := by
    show fderiv ℝ (dz fun q => b q i) p (0, 1) = fderiv ℝ (fun q => dz b q i) p (0, 1)
    rw [e2.fderiv_eq]
  simp only [lapMer]
  rw [a1, a2, dρ_proj hdρd, dz_proj hdzd, dρ_proj (hdb p hpm), PiLp.add_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]


theorem vecLapMer_mp_of (h1 : MpSmooth) (h2 : MpDRho) (h3 : MpDZ) (h4 : SqrtQ) (h5 : SqrtEta)
    {R τ : ℝ} (F : Coord → Merid) (hR : 0 < R) (hF : ContDiffOn ℝ ∞ F halfC)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    vecLapMer (mp R τ F) p = mp R τ (lapReal R⁻¹ F) p := by
  have hpm : p ∈ halfM := ⟨hp, trivial⟩
  have hnh : halfM ∈ 𝓝 p := isOpen_halfM.mem_nhds hpm
  have hQF := contDiffOn_classQg (ε := R⁻¹) hF
  have hEF := contDiffOn_classEtaG hF
  have hG1 := contDiffOn_halfC_sqrt_smul hQF
  have hG2 := contDiffOn_halfC_sqrt_smul hEF
  have hm := h1 R τ F hR hF
  have hrr : dρ (dρ (mp R τ F)) p =
      mp R τ (fun x => x.1 • (classQg R⁻¹ (classQg R⁻¹ F) x - R⁻¹ • classQg R⁻¹ F x)) p := by
    have e : dρ (mp R τ F) =ᶠ[𝓝 p] mp R τ (fun x => √x.1 • classQg R⁻¹ F x) := by
      filter_upwards [hnh] with q hq using h2 R τ F hR hF q hq.1
    have : dρ (dρ (mp R τ F)) p = dρ (mp R τ (fun x => √x.1 • classQg R⁻¹ F x)) p := by
      show fderiv ℝ (dρ (mp R τ F)) p (1, 0) = fderiv ℝ (mp R τ (fun x => √x.1 • classQg R⁻¹ F x)) p (1, 0)
      rw [e.fderiv_eq]
    rw [this, h2 R τ _ hR hG1 p hp]
    apply mp_congr hR _ hp
    intro x hx
    have := h4 R⁻¹ (classQg R⁻¹ F) x hx hQF
    rw [this, smul_smul, Real.mul_self_sqrt hx.le]
  have hzz : dz (dz (mp R τ F)) p =
      mp R τ (fun x => x.1 • classEtaG (classEtaG F) x) p := by
    have e : dz (mp R τ F) =ᶠ[𝓝 p] mp R τ (fun x => √x.1 • classEtaG F x) := by
      filter_upwards [hnh] with q hq using h3 R τ F hR hF q hq.1
    have : dz (dz (mp R τ F)) p = dz (mp R τ (fun x => √x.1 • classEtaG F x)) p := by
      show fderiv ℝ (dz (mp R τ F)) p (0, 1) = fderiv ℝ (mp R τ (fun x => √x.1 • classEtaG F x)) p (0, 1)
      rw [e.fderiv_eq]
    rw [this, h3 R τ _ hR hG2 p hp]
    apply mp_congr hR _ hp
    intro x hx
    have := h5 (classEtaG F) x hx hEF
    rw [this, smul_smul, Real.mul_self_sqrt hx.le]
  have hr1 : dρ (mp R τ F) p = mp R τ (fun x => √x.1 • classQg R⁻¹ F x) p := h2 R τ F hR hF p hp
  have hc : (merChart R τ p).1 = R ^ 2 / p.1 ^ 2 := rfl
  have hs := sqrt_s hR hp
  have hs' : √((merChart R τ p).1) = R / p.1 := by rw [hc]; exact hs
  have hRp : R ≠ 0 := hR.ne'
  have hpp : p.1 ≠ 0 := hp.ne'
  ext i
  fin_cases i
  · show vecLapMer (mp R τ F) p 0 = _
    rw [vecLapMer_apply_zero, lapMer_proj hm hp 0, hrr, hr1, hzz]
    simp only [mp, lapReal, hoopRv, hc, hs, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul, PiLp.single_apply]
    field_simp
    simp
    ring
  · show vecLapMer (mp R τ F) p 1 = _
    rw [vecLapMer_apply_one, lapMer_proj hm hp 1, hrr, hr1, hzz]
    simp only [mp, lapReal, hoopRv, hc, hs, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul, PiLp.single_apply]
    simp [Fin.ext_iff]
    field_simp
    ring


/-- `LapNvReal` from the five first-order leaves. -/
theorem lapNvReal_of (h1 : MpSmooth) (h2 : MpDRho) (h3 : MpDZ) (h4 : SqrtQ) (h5 : SqrtEta) :
    LapNvReal := by
  intro R b hR hb t y hy
  have hsm := h1 R t b hR hb.contDiffOn
  rw [show (fun z => Nv R b t z) = liftMer (mp R t b) from Nv_eq_liftMer R b t,
    vecLap_liftMer hsm hy, Nv_eq_liftMer R (lapReal R⁻¹ b) t]
  have hp : 0 < (mer y).1 := ϱ_pos hy
  have := vecLapMer_mp_of h1 h2 h3 h4 h5 (τ := t) b hR hb.contDiffOn hp
  simp only [liftMer]
  rw [this]
  rfl


theorem fderiv_sqrt_smul {H : Coord → Merid} {x : Coord} (hx : 0 < x.1)
    (hH : DifferentiableAt ℝ H x) (v : Coord) :
    fderiv ℝ (fun y => √y.1 • H y) x v =
      √x.1 • fderiv ℝ H x v + ((1 / (2 * √x.1)) * v.1) • H x := by
  have hc : HasFDerivAt (fun y : Coord => √y.1)
      ((1 / (2 * √x.1)) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).sqrt hx.ne'
  have h2 := (hc.smul hH.hasFDerivAt).fderiv
  rw [show (fun y : Coord => √y.1 • H y) = ((fun y : Coord => √y.1) • H) from rfl, h2]
  simp

theorem diffAt_of_halfC {H : Coord → Merid} (hH : ContDiffOn ℝ ∞ H halfC) {x : Coord}
    (hx : 0 < x.1) : DifferentiableAt ℝ H x :=
  (hH.contDiffAt (isOpen_Ioi.prod isOpen_univ |>.mem_nhds ⟨hx, trivial⟩)).differentiableAt
    (by norm_num)

theorem sqrtEta_proof : SqrtEta := by
  intro H x hx hH
  unfold classEtaG
  rw [fderiv_sqrt_smul hx (diffAt_of_halfC hH hx)]
  simp [cdir]

theorem sqrtQ_proof : SqrtQ := by
  intro ε H x hx hH
  have hd := diffAt_of_halfC hH hx
  have hs : √x.1 ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hss : √x.1 * √x.1 = x.1 := Real.mul_self_sqrt hx.le
  unfold classQg
  simp only [Fin.sum_univ_three, fderiv_sqrt_smul hx hd, vQ, dQ, cdir]
  simp
  match_scalars <;> field_simp <;> first | (linear_combination ε * hss) | (linear_combination (-ε) * hss) | ring


theorem mpSmooth_proof : MpSmooth := by
  intro R τ F hR hF
  have hc := UnforcedLeray.B0186.contDiffOn_merChart hR.ne' τ
  have hmaps : MapsTo (merChart R τ) halfM halfC := fun p hp =>
    ⟨merChart_fst_pos hR hp.1, trivial⟩
  have h1 : ContDiffOn ℝ 2 (fun q => F (merChart R τ q)) halfM :=
    (hF.of_le (by simp)).comp hc hmaps
  have h2 : ContDiffOn ℝ 2 (fun q : ℝ × ℝ => R / q.1) halfM :=
    contDiffOn_const.fun_div contDiffOn_fst fun p hp => ne_of_gt hp.1
  refine (h2.smul h1).congr ?_
  intro q hq
  simp only [mp]
  rw [sqrt_s hR hq.1]
  rfl

theorem mp_hasDerivAt_rho {R τ : ℝ} (hR : 0 < R) {F : Coord → Merid} (hF : ContDiffOn ℝ ∞ F halfC)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    HasDerivAt (fun ρ : ℝ => mp R τ F (ρ, p.2))
      ((R / p.1) • fderiv ℝ F (merChart R τ p) (-(2 * R ^ 2 / p.1 ^ 3), (R / p.1, -(R * p.2 / p.1 ^ 2)))
        + (-(R / p.1 ^ 2)) • F (merChart R τ p)) p.1 := by
  have hd := diffAt_of_halfC hF (merChart_fst_pos (τ := τ) hR hp)
  have hF1 := hd.hasFDerivAt.comp_hasDerivAt p.1
    (hasDerivAt_merChart_fst hR.ne' τ p.2 hp.ne')
  have hs : HasDerivAt (fun ρ : ℝ => R / ρ) (-(R / p.1 ^ 2)) p.1 := by
    have h := (hasDerivAt_const p.1 R).div (hasDerivAt_id p.1) hp.ne'
    refine h.congr_deriv ?_
    simp [neg_div]
  have h3 := hs.smul hF1
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hp] with ρ hρ
  simp only [mp]
  rw [sqrt_s hR (p := (ρ, p.2)) hρ]
  rfl

theorem mpDRho_proof : MpDRho := by
  intro R τ F hR hF p hp
  have hnh : halfM ∈ 𝓝 p := isOpen_halfM.mem_nhds ⟨hp, trivial⟩
  have hmp : DifferentiableAt ℝ (mp R τ F) p :=
    ((mpSmooth_proof R τ F hR hF).contDiffAt hnh).differentiableAt (by norm_num)
  have hpath : HasDerivAt (fun ρ : ℝ => (ρ, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const _ _)
  have h1 := hmp.hasFDerivAt.comp_hasDerivAt p.1 hpath
  have h2 := mp_hasDerivAt_rho hR hF hp (τ := τ)
  have := h1.unique h2
  show fderiv ℝ (mp R τ F) p (1, 0) = _
  rw [this]
  have hc : (merChart R τ p).1 = R ^ 2 / p.1 ^ 2 := rfl
  have hη : (merChart R τ p).2.2 = R * p.2 / p.1 := rfl
  have hs := sqrt_s hR hp
  have hD : (-(2 * R ^ 2 / p.1 ^ 3), (R / p.1, -(R * p.2 / p.1 ^ 2))) =
      (-(2 * R ^ 2 / p.1 ^ 3)) • cdir 0 + (R / p.1) • cdir 1 + (-(R * p.2 / p.1 ^ 2)) • cdir 2 := by
    ext <;> simp [cdir]
  rw [hD, map_add, map_add, map_smul, map_smul, map_smul]
  have hRp : R ≠ 0 := hR.ne'
  have hpp : p.1 ≠ 0 := hp.ne'
  simp only [mp, classQg, Fin.sum_univ_three, vQ, dQ, hc, hη, hs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, smul_add, smul_smul]
  match_scalars <;> field_simp <;> ring


theorem mpDZ_proof : MpDZ := by
  intro R τ F hR hF p hp
  have hnh : halfM ∈ 𝓝 p := isOpen_halfM.mem_nhds ⟨hp, trivial⟩
  have hmp : DifferentiableAt ℝ (mp R τ F) p :=
    ((mpSmooth_proof R τ F hR hF).contDiffAt hnh).differentiableAt (by norm_num)
  have hpath : HasDerivAt (fun ζ : ℝ => (p.1, ζ)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id p.2)
  have h1 := hmp.hasFDerivAt.comp_hasDerivAt p.2 hpath
  have hd := diffAt_of_halfC hF (merChart_fst_pos (τ := τ) hR hp)
  have hF1 := hd.hasFDerivAt.comp_hasDerivAt p.2 (hasDerivAt_merChart_snd R τ (r := p.1) p.2)
  have h2 : HasDerivAt (fun ζ : ℝ => mp R τ F (p.1, ζ))
      (√(R ^ 2 / p.1 ^ 2) • fderiv ℝ F (merChart R τ p) ((0 : ℝ), ((0 : ℝ), R / p.1))) p.2 := by
    have h3 := hF1.const_smul (√(R ^ 2 / p.1 ^ 2))
    exact h3
  have := h1.unique h2
  show fderiv ℝ (mp R τ F) p (0, 1) = _
  rw [this]
  have hc : (merChart R τ p).1 = R ^ 2 / p.1 ^ 2 := rfl
  have hs := sqrt_s hR hp
  have hD : ((0 : ℝ), ((0 : ℝ), R / p.1)) = (R / p.1) • cdir 2 := by
    ext <;> simp [cdir]
  rw [hD, map_smul]
  have hRp : R ≠ 0 := hR.ne'
  have hpp : p.1 ≠ 0 := hp.ne'
  simp only [mp, classEtaG, hc, hs, smul_smul]

end UnforcedLeray.Short.IIb
