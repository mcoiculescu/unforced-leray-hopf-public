import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `repair:thin-complete` (source 5374-5506): the three-way split of the thin residual

Source of record: `the November 2 reference manuscript` (73 pages), lines
5374-5506.  For the thin old source `χ_oT₁` the Ward residual `E(U;X₁,Y₁)` is compared with the
Gaussian residual `E_{A_T}` (`A_T = 𝓛T₁`) in three steps:

* (a) `MeanComparisonAt` (5415-5448 with 5272-5289, 5506): replacing the response `X₁,Y₁` of
  the old source by the phase-mean zero-width Newton response `X^mt, Y^mt` (the lifts
  `Xmean, Ymean`) in the Ward residual costs `P_ν N(ε⁴ + ε^{85/22}e^{m₀/ν})` (`meanE` is the
  residual built from the mean lifts).  Against the raw-train coefficients (transversally
  localized, 5434-5436) the geometric comparison and Hessian bounds (5415-5448) give `P_ν ε⁴ N`;
  the remainder coefficients (repair `r_b`, entrance, `∇p - G_flat`, bounded only in `Y_{11/4}`)
  multiply `D(X₁-X^mt)`, `D(Y₁-Y^mt)`, `D²X` and are bounded only through the individual
  thin-source bound `‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22}N₁` by Hölder, i.e. by
  `P_ν ε^{85/22}e^{m₀/ν} N` (5272-5289; "the `85/22` term retains the entire Cartesian pressure
  correction", 5506);
* (b) `RingExpansionAt` (5449-5483 with 5272-5289, 5494-5506): the mean residual equals the
  affine ring expression `s^{3/2}{2B_Tv + 2νA_T:D²_flat v - (A_T+A_Tᵀ)∇_flat p_cyl}` (`ringAff`,
  with the *actual* train `v, p_cyl`) up to `P_ν N(ε⁴ + ε^{85/22}e^{m₀/ν})`; uses `ActualJet`
  (rep/6) and `JetClock` (rep/7).  `meanE` is built on the exact background `U = V + r_b` with
  the exact pressure, `ringAff` on the flat train, so the exact-pressure and repair-coefficient
  errors (`∇(p_raw - p_lift) = -(I-ℙ)F_raw`, `‖∇p - G_flat‖_{Y_{11/4}} ≤ P_ν ε^{3/11}e^{m₀/ν}`,
  `‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22}N₁`, exponent `1 + 3/11 + 57/22 = 85/22`, source
  5272-5289; "The `85/22` term retains the entire Cartesian pressure correction", 5505) lie in
  this step;
* (c) `GaussianReplaceAt` (5484-5498, 5272-5289): replacing the actual train and its pressure by
  the summed Gaussians (so `ringAff` by `E_{A_T}`, `EAcoef`) costs
  `P_ν N(ε³δ_base + ε^{85/22}e^{m₀/ν})` (its `85/22` term is slack: `ringAff - E_{A_T}` contains
  no exact pressure).

`thinCompleteAt_of` / `thinComplete_of` assemble the three bounds into `ThinCompleteAt` /
`ThinComplete`.  Measurability of `meanE` and `ringAff` (needed for the triangle inequality) is
part of (a) and (c) respectively.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The Ward residual with arbitrary `X, Y` -/

/-- The unprojected Ward residual (source 4276-4280) for arbitrary fields `X, Y` in place of
`wardX, wardY`: `2U·∇Y - 2νC_diff + (U⊗U):D²X - (DX+DXᵀ)∇p`.  (`μ, R` are unused: they enter
`wardE` only through `wardX/wardY`.) -/
def wardEXY (ν _μ _R : ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ)
    (X Y : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  (2 : ℝ) • fderiv ℝ (Y τ) y (U τ y) - (2 * ν) • physCdiff (U τ) (X τ) y +
    physUUD2 (U τ) (X τ) y - physDXp (X τ) (p τ) y

theorem wardE_eq_wardEXY (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField)
    (p : ℝ → Space → ℝ) (g : Chart → Ten3) :
    wardE ν μ R c χy U p g =
      wardEXY ν μ R U p (wardX ν μ R c χy g) (wardY ν μ R c χy g) := rfl

/-! ## 2. The mean-field lifts -/

/-- The phase-independent Newton field `X^mt` (source 5380-5382, 4785-4791) as a field on `Space`
(`WithLp` conversion of `Xmt : Vec3 → Vec3`), constant in the phase `τ`. -/
def Xmean (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) : ℝ → Space → Space :=
  fun _ y => WithLp.toLp 2 (Xmt c ν ε μ χo χy M (WithLp.ofLp y))

/-- `Y^mt = D_{μ+1}X^mt` (`YmtFun`, source 5380-5382, 5455) as a field on `Space`. -/
def Ymean (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) : ℝ → Space → Space :=
  fun _ y => WithLp.toLp 2 (YmtFun c ν ε μ χo χy M (WithLp.ofLp y))

/-! ## 3. The three residuals of a regime -/

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- A chart representative of the old thin source `χ_oT₁` of `T`: the sum of the two components
of `chiOStr (thinPart T)` (source 5377-5379, 4161); this is the `g₁ + g₂` of `IsWardTriple`. -/
def thinG (T : LStr Pl K L) : Chart → Ten3 :=
  ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T)).fst : Chart → Ten3) +
    ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T)).snd : Chart → Ten3)

/-- The coefficient of the actual Ward residual `E(U; X₁, Y₁)` of the old thin source
(source 4276-4280, 5377-5379). -/
def actualE (T : LStr Pl K L) : Chart → Merid :=
  coefOf L.ε⁻¹ (wardE L.ν μ L.ε⁻¹ (cOf L.ν) K.χy L.U L.pres (thinG Pl K L T))

/-- The mean Ward residual (source 5380-5382, 5455, 5415-5448): the Ward residual with the
phase-mean zero-width Newton fields `X^mt, Y^mt` of `M = thinRep T` and the same stream cutoff. -/
def meanE (T : LStr Pl K L) : Chart → Merid :=
  coefOf L.ε⁻¹ (wardEXY L.ν μ L.ε⁻¹ L.U L.pres
    (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T))
    (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)))

/-- The flat-frame velocity profile `v(s, q, η)` of the actual train of the level (source
5466-5483), as a meridional vector `(v_q, v_η)`. -/
def trainV (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (L.train.v s x 0, L.train.v s x 1)

/-- The flat-frame pressure `p_cyl(s, q, η)` of the actual train of the level (source 5466-5483). -/
def trainP (s : ℝ) (x : ℝ × ℝ) : ℝ := L.train.p s x

end Regime

/-- The affine expression of the ring chart (source 5466-5483, `eA` of 4969-4985) for an
arbitrary flat profile `(vv, pp)`: `2Bv + 2νA^y:D²_flat v - (A^y + (A^y)ᵀ)∇_flat p`, `B = Bmat`.
For `vv = V_j, pp = p_j` and a sum over `j` this is `eA`. -/
def ringAffGen (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (vv : ℝ → ℝ × ℝ → ℝ × ℝ)
    (pp : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) : Vec3 :=
  (2 : ℝ) • mv (Bmat ν μ χf A s) (emb (vv s x)) +
    (2 * ν) • hessContr (Ay ν χf A s) (vv s) x -
    mv (fun a b => Ay ν χf A s a b + Ay ν χf A s b a) (emb (mgrad (pp s) x))

/-- `eA` is the lattice sum of `ringAffGen` over the Gaussian profiles `V_j, p_j`. -/
theorem eA_eq_tsum_ringAffGen (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    eA ν μ χf A s x = ∑' j : ℤ,
      ringAffGen ν μ χf A (fun s' => Vj ν s' j) (fun s' => pj ν s' j) s x := rfl

/-- The chart coefficient `s^{-1/2}(·)_{(r,z)}` of `s^{3/2}·ringAffGen` (the convention of
`EAcoef`, `EA = s^{3/2}eA`). -/
def ringAffCoef (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (vv : ℝ → ℝ × ℝ → ℝ × ℝ)
    (pp : ℝ → ℝ × ℝ → ℝ) (p : Chart) : Merid :=
  merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) • ringAffGen ν μ χf A vv pp p.1 p.2))

/-- Compatibility with `EAcoef`: it is `ringAffCoef` with `eA` in place of `ringAffGen`. -/
theorem EAcoef_eq (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (p : Chart) :
    EAcoef ν μ χf A p = merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) • eA ν μ χf A p.1 p.2)) :=
  rfl

section Regime2

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **The ring expression with the actual train** (source 5466-5483): the chart coefficient of
`s^{3/2}{2B_Tv + 2νA_T:D²_flat v - (A_T+A_Tᵀ)∇_flat p_cyl}`, `A_T = 𝓛T₁ = LjFun`,
`B_T = Bmat A_T`, with `v, p_cyl` the flat-frame profiles of `L.train`. -/
def ringAff (T : LStr Pl K L) : Chart → Merid :=
  ringAffCoef L.ν μ K.χf
    (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
    (trainV L) (trainP L)

/-- **(a) mean comparison** (source 5415-5448; `IIIa sep:mean-comparison` SP 3767-3780): the
mean Ward residual `meanE` is measurable and differs from the actual one by
`P_ν N(ε⁴ + ε^{85/22}e^{m₀/ν})` in `L²(srcMeasure)` (the `85/22` term: the remainder coefficients
`r_b`, entrance, pressure correction, bounded only in `Y_{11/4}`, source 5272-5289, 5415-5448). -/
def MeanComparisonAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L,
    AEStronglyMeasurable (meanE Pl K L μ T) (srcMeasure (cOf L.ν)) ∧
    eLpNorm (actualE Pl K L μ T - meanE Pl K L μ T) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k *
        (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T

/-- **(b) ring expansion** (source 5449-5483 with the exact-pressure and repair-coefficient errors
of 5272-5289, 5494-5506): `‖meanE - ringAff‖ ≤ P_ν N(ε⁴ + ε^{85/22}e^{m₀/ν})`.  The `ε⁴` part is
the substitution of the ring-chart rules and the jet clock (uses the actual-jet (5400-5413) and
exact-jet-clock (5449-5458) estimates); the `ε^{85/22}e^{m₀/ν}` part is the replacement of `U` by
`U_raw` and of the exact pressure by the flat lifted pressure (`meanE` uses `L.U`, `L.pres`;
`ringAff` the flat train). -/
def RingExpansionAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L,
    eLpNorm (meanE Pl K L μ T - ringAff Pl K L μ T) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k *
        (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T

/-- **(c) Gaussian replacement** (source 5484-5498, 5272-5289): `ringAff` is measurable and
differs from `E_{A_T}` (`EAcoef` of `A_T`) by `P_ν N(ε³δ_base + ε^{85/22}e^{m₀/ν})`. -/
def GaussianReplaceAt (C : ℝ) (k : ℕ) (Csig bsig : ℝ) : Prop :=
  ∀ T : LStr Pl K L,
    AEStronglyMeasurable (ringAff Pl K L μ T) (srcMeasure (cOf L.ν)) ∧
    eLpNorm (ringAff Pl K L μ T -
        EAcoef L.ν μ K.χf
          (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T))
        2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k *
        (L.ε ^ 3 * deltaBase Csig bsig L.ν + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) *
        oldN1 Pl K L T

end Regime2

/-! ## 4. The sequence forms -/

namespace SeqData

variable (D : SeqData)

/-- (a) along the sequence. -/
def MeanComparison : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    MeanComparisonAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- (b) along the sequence. -/
def RingExpansion : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    RingExpansionAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- (c) along the sequence. -/
def GaussianReplace : Prop :=
  ∃ (C : ℝ) (k : ℕ) (Csig bsig : ℝ), 0 < bsig ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    GaussianReplaceAt D.Pl D.K (D.level n) (D.mu n z) C k Csig bsig

end SeqData

/-! ## 5. Assembly -/

theorem bound_mono {x N : ℝ≥0∞} {ν F C C' : ℝ} {k k' : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hF : 0 ≤ F) (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k')
    (h : x ≤ ENNReal.ofReal (C * ν⁻¹ ^ k * F) * N) :
    x ≤ ENNReal.ofReal (C' * ν⁻¹ ^ k' * F) * N := by
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have h1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hP : ν⁻¹ ^ k ≤ ν⁻¹ ^ k' := pow_le_pow_right₀ h1 hk
  have hP0 : 0 ≤ ν⁻¹ ^ k := by positivity
  calc C * ν⁻¹ ^ k * F ≤ C' * ν⁻¹ ^ k * F :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hP0) hF
    _ ≤ C' * ν⁻¹ ^ k' * F :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hC') hF

section Assembly

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **`thinCompleteAt_of`**: the three bounds give `ThinCompleteAt` at one regime. -/
theorem thinCompleteAt_of (hpin : RegimePins Pl K L μ) {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    {Csig bsig : ℝ} (h1 : MeanComparisonAt Pl K L μ C k) (h2 : RingExpansionAt Pl K L μ C k)
    (h3 : GaussianReplaceAt Pl K L μ C k Csig bsig) :
    ThinCompleteAt Pl K L μ (3 * C) k Csig bsig := by
  intro T
  set μs := srcMeasure (cOf L.ν) with hμs
  set W := (wardOps Pl K L μ).2.2 (thinPart T) with hW
  set E := EAOp K L μ (LjOp Pl K L μ T) with hE
  set A := LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T with hA
  have hward := Classical.epsilon_spec hpin.ward
  have hWae : (W : Chart → Merid) =ᵐ[μs] actualE Pl K L μ T :=
    (hward (thinPart T) _ _ Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl).2.2
  have hLj : affIota K.as (LjOp Pl K L μ T) = A := Classical.epsilon_spec hpin.lj T
  have hEae : (E : Chart → Merid) =ᵐ[μs] EAcoef L.ν μ K.χf A := by
    have := EAOp_spec hpin.eA (LjOp Pl K L μ T)
    rwa [hLj] at this
  obtain ⟨hm1, b1⟩ := h1 T
  obtain ⟨hr3, b3⟩ := h3 T
  have b2 := h2 T
  have hfm : AEStronglyMeasurable (actualE Pl K L μ T) μs :=
    (Lp.aestronglyMeasurable W).congr hWae
  have hem : AEStronglyMeasurable (EAcoef L.ν μ K.χf A) μs :=
    (Lp.aestronglyMeasurable E).congr hEae
  -- norm as eLpNorm
  have hnorm : ENNReal.ofReal ‖W - E‖ =
      eLpNorm (actualE Pl K L μ T - EAcoef L.ν μ K.χf A) 2 μs := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub W E, hWae, hEae] with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    rfl
  rw [hnorm]
  have hsplit : actualE Pl K L μ T - EAcoef L.ν μ K.χf A =
      (actualE Pl K L μ T - meanE Pl K L μ T) +
        ((meanE Pl K L μ T - ringAff Pl K L μ T) +
          (ringAff Pl K L μ T - EAcoef L.ν μ K.χf A)) := by
    funext p; simp only [Pi.add_apply, Pi.sub_apply]; abel
  have t1 : eLpNorm (actualE Pl K L μ T - EAcoef L.ν μ K.χf A) 2 μs ≤
      eLpNorm (actualE Pl K L μ T - meanE Pl K L μ T) 2 μs +
        (eLpNorm (meanE Pl K L μ T - ringAff Pl K L μ T) 2 μs +
          eLpNorm (ringAff Pl K L μ T - EAcoef L.ν μ K.χf A) 2 μs) := by
    rw [hsplit]
    refine (eLpNorm_add_le (hfm.sub hm1) ((hm1.sub hr3).add (hr3.sub hem)) (by norm_num)).trans ?_
    gcongr
    exact eLpNorm_add_le (hm1.sub hr3) (hr3.sub hem) (by norm_num)
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hP : 0 ≤ L.ν⁻¹ ^ k := by positivity
  have hδ : 0 ≤ deltaBase Csig bsig L.ν := (Real.exp_pos _).le
  have hX : 0 ≤ L.ε ^ 3 * deltaBase Csig bsig L.ν + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) := by
    positivity
  set N := oldN1 Pl K L T
  set a2 := C * L.ν⁻¹ ^ k *
    (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) with ha2
  set b := C * L.ν⁻¹ ^ k *
    (L.ε ^ 3 * deltaBase Csig bsig L.ν + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) with hb
  have ha20 : 0 ≤ a2 := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hz : 0 ≤ C * L.ν⁻¹ ^ k * (L.ε ^ 3 * deltaBase Csig bsig L.ν) := by positivity
  have hz2 : 0 ≤ C * L.ν⁻¹ ^ k * (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := ha20
  calc eLpNorm (actualE Pl K L μ T - EAcoef L.ν μ K.χf A) 2 μs
      ≤ ENNReal.ofReal a2 * N + (ENNReal.ofReal a2 * N + ENNReal.ofReal b * N) :=
        t1.trans (add_le_add b1 (add_le_add b2 b3))
    _ = ENNReal.ofReal (a2 + (a2 + b)) * N := by
        rw [ENNReal.ofReal_add ha20 (add_nonneg ha20 hb0), ENNReal.ofReal_add ha20 hb0]
        ring
    _ ≤ ENNReal.ofReal (3 * C * L.ν⁻¹ ^ k * (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) *
          Real.exp (K.m0 / L.ν) + L.ε ^ 3 * deltaBase Csig bsig L.ν)) * N := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [ha2, hb]
        have hx : 0 ≤ C * L.ν⁻¹ ^ k * L.ε ^ 4 := by positivity
        nlinarith [hz, hx]

end Assembly

/-- **`thinComplete_of`**: the three sequence bounds give `ThinComplete` (source 5484-5506). -/
theorem thinComplete_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : D.MeanComparison) (h2 : D.RingExpansion) (h3 : D.GaussianReplace) :
    D.ThinComplete := by
  obtain ⟨C1, k1, e1⟩ := h1
  obtain ⟨C2, k2, e2⟩ := h2
  obtain ⟨C3, k3, Csig, bsig, hb, e3⟩ := h3
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  set C : ℝ := |C1| + |C2| + |C3| with hCdef
  set k : ℕ := max k1 (max k2 k3) with hk
  have hC0 : 0 ≤ C := by positivity
  refine ⟨3 * C, k, Csig, bsig, hb, ?_⟩
  filter_upwards [e1, e2, e3, hle, hst.pins] with n a1 a2 a3 hν hp z hz
  have hνp := (D.level n).ν_pos
  have hν1 : (D.level n).ν ≤ 1 := hν.1
  have hε := (D.level n).ε_pos
  have hC1 : C1 ≤ C := (le_abs_self C1).trans (by rw [hCdef]; linarith [abs_nonneg C2, abs_nonneg C3])
  have hC2 : C2 ≤ C := (le_abs_self C2).trans (by rw [hCdef]; linarith [abs_nonneg C1, abs_nonneg C3])
  have hC3 : C3 ≤ C := (le_abs_self C3).trans (by rw [hCdef]; linarith [abs_nonneg C2, abs_nonneg C1])
  refine thinCompleteAt_of D.Pl D.K (D.level n) (D.mu n z) (hp z hz) hC0 ?_ ?_ ?_
  · intro T
    obtain ⟨m, b⟩ := a1 z hz T
    exact ⟨m, bound_mono hνp hν1 (by positivity) hC1 hC0 (le_max_left _ _) b⟩
  · intro T
    exact bound_mono hνp hν1 (by positivity) hC2 hC0
      ((le_max_left k2 k3).trans (le_max_right _ _)) (a2 z hz T)
  · intro T
    obtain ⟨m, b⟩ := a3 z hz T
    refine ⟨m, bound_mono hνp hν1 (by unfold deltaBase; positivity) hC3 hC0
      ((le_max_right k2 k3).trans (le_max_right _ _)) b⟩

end UnforcedLeray.Short.PartIIIb.Concrete
