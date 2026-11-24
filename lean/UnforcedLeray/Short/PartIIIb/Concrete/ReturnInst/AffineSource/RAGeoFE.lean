import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.FEPer

/-!
# `PartIII-b:C/asrc/ra/9/3` : the FE piece of `RAGeoBound` is identically zero (source 4981)

Source of record: `the November 2 reference manuscript` (73 pages), lines 4963-4975
(lattice sums), 4981 (`FAcoef = s f_A`, `EAcoef = s e_A`), 5034-5044 (the four pieces).

The piece `geoFEPiece` is `coefOf ε⁻¹ (feLift) - s·(f_A + e_A)`.  For `s > 0`:
* the ring lift inverts the chart coefficient: `coefOf R (Nv R b) p = b p` (`fe_coefOf_Nv`,
  chart round trip `fe_chart_roundtrip`);
* `perExt c` replaces the argument by its cell representative, and `F_A + E_A` is
  `c`-periodic in `q` (`affFEPer`), so the lift at `(s, x)` is `(FAcoef + EAcoef)(s, x)`;
* `FAcoef + EAcoef = s·(f_A + e_A)` in the chart (`fe_FAcoef_add_eq`, using `F_A = s^{3/2}f_A`).

Hence the piece vanishes at every chart point with `s > 0`, which gives every clause of
`RAGeoPieceBound` (the measure of `srcMeasure` is carried by `s > 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The ring chart of the lift -/

/-- The similarity point `y = chartY R p` of the chart point `p = (s, (q, η))`, `s > 0`:
its radial coordinate is `R/√s`, its axial coordinate `η/√s`, the age is `s`. -/
theorem fe_chartY_facts {R : ℝ} (hR : 0 < R) (p : Chart) (hp : 0 < p.1) :
    NearInst.chartY R p 0 = R / Real.sqrt p.1 ∧ NearInst.chartY R p 1 = 0 ∧
      ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 ∧
      Axi.age R (NearInst.chartY R p) = p.1 := by
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hy0 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by simp [NearInst.chartY]
  have hy1 : NearInst.chartY R p 1 = 0 := by simp [NearInst.chartY]
  have hϱ : ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
    unfold ϱ
    rw [hy0, hy1, show (R / Real.sqrt p.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt p.1) ^ 2 by ring]
    exact Real.sqrt_sq (div_nonneg hR.le hs.le)
  refine ⟨hy0, hy1, hϱ, ?_⟩
  have hR0 : R ≠ 0 := hR.ne'
  unfold Axi.age
  rw [hϱ, div_pow, Real.sq_sqrt hp.le]
  field_simp

/-- The chart point of the phase `τ = chartTau R p` and the similarity point `y = chartY R p`
is `p` itself (`age = s`, `trans = η`, `phase = q`). -/
theorem fe_chart_roundtrip {R : ℝ} (hR : 0 < R) (p : Chart) (hp : 0 < p.1) :
    Axi.chart R (NearInst.chartTau R p) (NearInst.chartY R p) = p := by
  obtain ⟨hy0, hy1, hϱ, hage⟩ := fe_chartY_facts hR p hp
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hR0 : R ≠ 0 := hR.ne'
  have hsq : Real.sqrt p.1 ≠ 0 := hs.ne'
  have htrans : Axi.trans R (NearInst.chartY R p) = p.2.2 := by
    unfold Axi.trans
    rw [hϱ, show NearInst.chartY R p 2 = p.2.2 / Real.sqrt p.1 by simp [NearInst.chartY]]
    field_simp
  have hphase : Axi.phase R (NearInst.chartTau R p) (NearInst.chartY R p) = p.2.1 := by
    unfold Axi.phase NearInst.chartTau
    rw [hage]
    field_simp
    ring
  unfold Axi.chart
  rw [hage, hphase, htrans]

/-- **The ring lift inverts the chart coefficient** (source 2666-2668, 4979-4981): for `s > 0`,
`coefOf R (Nv R b) p = b p` for every chart profile `b`. -/
theorem fe_coefOf_Nv {R : ℝ} (hR : 0 < R) (b : Chart → Merid) (p : Chart) (hp : 0 < p.1) :
    coefOf R (fun τ y => Nv R b τ y) p = b p := by
  obtain ⟨hy0, hy1, hϱ, hage⟩ := fe_chartY_facts hR p hp
  have hrt := fe_chart_roundtrip hR p hp
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hne : R / Real.sqrt p.1 ≠ 0 := div_ne_zero hR.ne' hs.ne'
  unfold coefOf
  simp only [Nv, frameL_apply, hrt, hage]
  ext i
  fin_cases i
  · simp [hy0, hϱ, hne, hs.ne']
  · simp [hy0, hϱ, hne, hs.ne']

/-! ## 2. The identity `FAcoef + EAcoef = s·(f_A + e_A)` in the chart (source 4981) -/

/-- `√s⁻¹ · s^{3/2} = s` for `s > 0`. -/
theorem fe_sqrt_inv_mul_rpow {s : ℝ} (hs : 0 < s) :
    (Real.sqrt s)⁻¹ * s ^ (3 / 2 : ℝ) = s := by
  have h32 : s ^ (3 / 2 : ℝ) = Real.sqrt s * s := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hs,
      Real.rpow_one]
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  rw [h32, ← mul_assoc, inv_mul_cancel₀ hsq, one_mul]

/-- **`F_A + E_A` in the chart** (source 4981): `FAcoef + EAcoef = s·(merPl f_A + merPl e_A)` at
`s > 0`, since `F_A = s^{3/2} f_A` and `E_A = s^{3/2} e_A`. -/
theorem fe_FAcoef_add_eq (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (hs : 0 < s)
    (x : ℝ × ℝ) :
    (FAcoef ν μ χ A + EAcoef ν μ χ A) (s, x) =
      s • toMer (merPl (fA ν μ χ A s x) + merPl (eA ν μ χ A s x)) := by
  have e : ∀ v : Vec3, (Real.sqrt s)⁻¹ • (s ^ (3 / 2 : ℝ) • v) = s • v := by
    intro v
    rw [smul_smul, fe_sqrt_inv_mul_rpow hs]
  show merOf ((Real.sqrt s)⁻¹ • (s ^ (3 / 2 : ℝ) • fA ν μ χ A s x)) +
      merOf ((Real.sqrt s)⁻¹ • (s ^ (3 / 2 : ℝ) • eA ν μ χ A s x)) =
    s • toMer (merPl (fA ν μ χ A s x) + merPl (eA ν μ χ A s x))
  rw [e, e, affMerOf_smul, affMerOf_smul, toMer_add, smul_add]
  rfl

/-! ## 3. Periodicity of the cell representative -/

/-- A `c`-periodic function is unchanged by the cell representative. -/
theorem cellRep_eq_of_periodic {c : ℝ} {E : Type*} (f : ℝ → E) (hf : Function.Periodic f c) (ξ : ℝ) :
    f (cellRep c ξ) = f ξ := by
  have e : cellRep c ξ = ξ - (⌊(ξ + c / 2) / c⌋ : ℝ) * c := by
    unfold cellRep
    ring
  rw [e]
  exact hf.sub_int_mul_eq _

/-! ## 4. The FE piece vanishes for `s > 0` -/

/-- **`geoFEPiece` vanishes on the chart for `s > 0`** (source 4981, 4963-4975): the lift of
`FAcoef + EAcoef` read through `perExt` is `(FAcoef + EAcoef)` at the cell representative, which
is the value at `(s, x)` by `c`-periodicity; and `FAcoef + EAcoef = s(f_A + e_A)`. -/
theorem geoFE_zero (as : ℝ) (χf : ℝ → ℝ) (p : Params) (μ : ℝ) (A : ℝ → Mat3)
    (hχ : IsSourceCutoffC χf) (hA : IsAffElem as A) (hc : p.c = cOf p.ν)
    (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) : geoFEPiece p μ χf A (s, x) = 0 := by
  have hR : 0 < p.ε⁻¹ := inv_pos.2 p.ε_pos
  have hper := affFEPer as χf hχ p.ν μ p.ν_pos A hA s x.2 hs
  have hcell : (FAcoef p.ν μ χf A + EAcoef p.ν μ χf A) (s, (cellRep p.c x.1, x.2)) =
      (FAcoef p.ν μ χf A + EAcoef p.ν μ χf A) (s, x) := by
    rw [hc]
    exact cellRep_eq_of_periodic
      (fun ξ => (FAcoef p.ν μ χf A + EAcoef p.ν μ χf A) (s, (ξ, x.2))) hper x.1
  have hlift : coefOf p.ε⁻¹ (feLift p.ν μ p.ε p.c χf A) (s, x) =
      (FAcoef p.ν μ χf A + EAcoef p.ν μ χf A) (s, (cellRep p.c x.1, x.2)) :=
    fe_coefOf_Nv hR (perExt p.c (FAcoef p.ν μ χf A + EAcoef p.ν μ χf A)) (s, x) hs
  unfold geoFEPiece
  rw [Pi.sub_apply, hlift, hcell, fe_FAcoef_add_eq p.ν μ χf A s hs x]
  simp

/-! ## 5. The leaf -/

/-- **Leaf FE** (source 4981): the FE piece of `RAGeoBound` satisfies `RAGeoPieceBound`. -/
theorem rAGeoFE (as : ℝ) (χf : ℝ → ℝ) : RAGeoFELeaf as χf := by
  intro hχ K hK hKs dm dp hdm
  refine ⟨1, 0, 1, one_pos, fun p d hreg hν μ hμ A hA => ?_⟩
  have hc : p.c = cOf p.ν := hreg.c_eq
  have hzero : ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ, geoFEPiece p μ χf A (s, x) = 0 :=
    fun s hs x => geoFE_zero as χf p μ A hχ hA hc s hs x
  have hae : geoFEPiece p μ χf A =ᵐ[srcMeasure p.c] 0 := by
    filter_upwards [ae_srcMeasure_fst_pos p.c] with z hz
    exact hzero z.1 hz z.2
  refine ⟨aestronglyMeasurable_zero.congr hae.symm, ?_, ?_, ?_⟩
  · intro s hs x
    have hs0 : 0 < s := lt_trans (div_pos (by norm_num) p.ν_pos) hs
    exact hzero s hs0 x
  · intro s hs
    have hfun : (fun x : ℝ × ℝ => geoFEPiece p μ χf A (s, x)) = fun _ => 0 :=
      funext fun x => hzero s hs x
    rw [hfun]
    exact aestronglyMeasurable_const
  · intro s hs _
    have h0 : ∀ x : ℝ × ℝ, ENNReal.ofReal (‖geoFEPiece p μ χf A (s, x)‖ ^ 2) = 0 :=
      fun x => by
        rw [hzero s hs x, norm_zero]
        simp
    simp only [h0, lintegral_zero]
    exact zero_le

end UnforcedLeray.Short.PartIIIb.Concrete
