import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Young
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.Scale
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSmooth

/-!
# Decomposition of `jetClock` (`PartIII-b:C/rep/7`, source 5438-5458, `repair:exact-jet-clock`)

Proved here: the exact identity `B_T = B_j + (ν/s)D_yΔ_yX^mt(R/√s,0,0)` (5454-5458), the `ε`-scaling of
the third derivative, and the assembly.  The only analytic input is `ClockEps1W`: the `ε = 1`
degree `-7` kernel bound for `D_yΔ_yX^mt` (stated directly against `oldN1 = N₁(χ_oT₁)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace JetClockCore

variable {X : Vec3 → Vec3}

theorem dX_hasFDeriv (hX : ContDiff ℝ 3 X) (y : Vec3) :
    HasFDerivAt (fderiv ℝ X) (fderiv ℝ (fderiv ℝ X) y) y :=
  ((hX.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num) y).hasFDerivAt

theorem apply_hasFDeriv (hX : ContDiff ℝ 3 X) (y e : Vec3) :
    HasFDerivAt (fun y' => fderiv ℝ X y' e)
      ((ContinuousLinearMap.apply ℝ Vec3 e).comp (fderiv ℝ (fderiv ℝ X) y)) y :=
  (ContinuousLinearMap.apply ℝ Vec3 e).hasFDerivAt.comp y (dX_hasFDeriv hX y)

theorem fderiv_apply_eq (hX : ContDiff ℝ 3 X) (y e v : Vec3) :
    fderiv ℝ (fun y' => fderiv ℝ X y' e) y v = fderiv ℝ (fderiv ℝ X) y v e := by
  rw [(apply_hasFDeriv hX y e).fderiv]; rfl

theorem vecLap_eq (hX : ContDiff ℝ 3 X) : vecLap X =
    fun y => ∑ j : Fin 3, fderiv ℝ (fderiv ℝ X) y (Pi.single j 1) (Pi.single j 1) := by
  funext y
  unfold vecLap
  refine Finset.sum_congr rfl fun j _ => ?_
  exact fderiv_apply_eq hX y _ _

theorem vecLap_diff (hX : ContDiff ℝ 3 X) : Differentiable ℝ (vecLap X) := by
  rw [vecLap_eq hX]
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ X)) :=
    (hX.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  refine Differentiable.fun_sum fun j _ => ?_
  have : ContDiff ℝ 1 (fun y => fderiv ℝ (fderiv ℝ X) y (Pi.single j 1) (Pi.single j 1)) :=
    (h2.clm_apply contDiff_const).clm_apply contDiff_const
  exact this.differentiable (by norm_num)

/-- The ray point `(R/√s, 0, 0)`. -/
def gam (ε s : ℝ) : Vec3 := ![ε⁻¹ / Real.sqrt s, 0, 0]

theorem hasDerivAt_gam {ε s : ℝ} (hs : 0 < s) :
    HasDerivAt (gam ε) (-(1 / (2 * s)) • gam ε s) s := by
  have hq0 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have h1 : HasDerivAt (fun s' => ε⁻¹ / Real.sqrt s') (-(1 / (2 * s)) * (ε⁻¹ / Real.sqrt s)) s := by
    have hq := ((Real.hasDerivAt_sqrt hs.ne').inv hq0).const_mul ε⁻¹
    have e : (fun s' => ε⁻¹ / Real.sqrt s') = fun s' => ε⁻¹ * (Real.sqrt s')⁻¹ := by
      funext s'; rw [div_eq_mul_inv]
    rw [e]
    refine hq.congr_deriv ?_
    rw [Real.sq_sqrt hs.le]
    field_simp
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [gam] using h1
  · simpa [gam] using hasDerivAt_const s (0 : ℝ)
  · simpa [gam] using hasDerivAt_const s (0 : ℝ)

/-- `Y = (-½y·∇ - νΔ + μ + ½)X`. -/
def Yf (X : Vec3 → Vec3) (ν μ : ℝ) (y : Vec3) : Vec3 :=
  -(1 / 2 : ℝ) • fderiv ℝ X y y - ν • vecLap X y + (μ + 1 / 2) • X y

/-- `A(s) = D_yX(R/√s,0,0)` for `s > 0`, zero otherwise (`Lpt`). -/
def Af (X : Vec3 → Vec3) (ε : ℝ) (s : ℝ) : Mat3 :=
  if 0 < s then fun i j => fderiv ℝ X (gam ε s) (Pi.single j 1) i else 0

theorem hasFDeriv_Yf (hX : ContDiff ℝ 3 X) (ν μ : ℝ) (y : Vec3) :
    HasFDerivAt (Yf X ν μ)
      ((-(1 / 2 : ℝ)) • ((fderiv ℝ X y) + (fderiv ℝ (fderiv ℝ X) y).flip y)
        - ν • fderiv ℝ (vecLap X) y + (μ + 1 / 2) • fderiv ℝ X y) y := by
  have h1 : HasFDerivAt (fun y' => fderiv ℝ X y' y')
      (fderiv ℝ X y + (fderiv ℝ (fderiv ℝ X) y).flip y) y := by
    have := (dX_hasFDeriv hX y).clm_apply (hasFDerivAt_id y)
    rwa [ContinuousLinearMap.comp_id] at this
  have h2 : HasFDerivAt (vecLap X) (fderiv ℝ (vecLap X) y) y :=
    ((vecLap_diff hX) y).hasFDerivAt
  have h3 : HasFDerivAt X (fderiv ℝ X y) y :=
    ((hX.differentiable (by norm_num)) y).hasFDerivAt
  have e : Yf X ν μ = (-(1 / 2 : ℝ) • fun y' => fderiv ℝ X y' y') - ν • vecLap X +
      (μ + 1 / 2) • X := by
    funext y'; simp [Yf]
  rw [e]
  have := ((h1.const_smul (-(1 / 2 : ℝ))).sub (h2.const_smul ν)).add (h3.const_smul (μ + 1 / 2))
  exact this

theorem hasDerivAt_entry (hX : ContDiff ℝ 3 X) (ε : ℝ) {s : ℝ} (hs : 0 < s) (i : Fin 3) (e : Vec3) :
    HasDerivAt (fun s' => fderiv ℝ X (gam ε s') e i)
      (-(1 / (2 * s)) * fderiv ℝ (fderiv ℝ X) (gam ε s) (gam ε s) e i) s := by
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp
    (gam ε s) (apply_hasFDeriv hX (gam ε s) e)
  have h2 := h1.comp_hasDerivAt s (hasDerivAt_gam (ε := ε) hs)
  refine h2.congr_deriv ?_
  simp [map_smul]

theorem deriv_Af (hX : ContDiff ℝ 3 X) (ε : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Af X ε) (fun i j => -(1 / (2 * s)) *
      fderiv ℝ (fderiv ℝ X) (gam ε s) (gam ε s) (Pi.single j 1) i) s := by
  have hev : Af X ε =ᶠ[nhds s] fun s' i j => fderiv ℝ X (gam ε s') (Pi.single j 1) i := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp [Af, show 0 < t from ht]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  exact hasDerivAt_entry hX ε hs i (Pi.single j 1)

theorem clock_identity (hX : ContDiff ℝ 3 X) (ε ν μ : ℝ) {s : ℝ} (hs : 0 < s) :
    deriv (Af X ε) s + (μ / s) • Af X ε s =
      (fun i j => s⁻¹ * fderiv ℝ (Yf X ν μ) (gam ε s) (Pi.single j 1) i) +
        fun i j => (ν / s) * fderiv ℝ (vecLap X) (gam ε s) (Pi.single j 1) i := by
  rw [(deriv_Af hX ε hs).deriv]
  funext i j
  have hsym := (hX.contDiffAt (x := gam ε s)).isSymmSndFDerivAt (by simp [minSmoothness]; norm_num)
  rw [(hasFDeriv_Yf hX ν μ (gam ε s)).fderiv]
  have hs0 : s ≠ 0 := hs.ne'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Af, if_pos hs,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.flip_apply]
  rw [hsym (Pi.single j 1) (gam ε s)]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem fderiv_scale {f : Vec3 → Vec3} (a ε : ℝ) {y : Vec3} (hf : DifferentiableAt ℝ f (ε • y)) :
    fderiv ℝ (fun y' => a • f (ε • y')) y = (a * ε) • fderiv ℝ f (ε • y) := by
  have h1 : HasFDerivAt (fun y' : Vec3 => ε • y') (ε • ContinuousLinearMap.id ℝ Vec3) y :=
    (hasFDerivAt_id y).const_smul ε
  have h2 : HasFDerivAt (fun y' => a • f (ε • y')) (a • (fderiv ℝ f (ε • y)).comp
      (ε • ContinuousLinearMap.id ℝ Vec3)) y := (hf.hasFDerivAt.comp y h1).const_smul a
  rw [h2.fderiv]
  ext v k
  simp [mul_assoc]

/-- The scaled field `ε² X(ε·)`. -/
def Xsc (X : Vec3 → Vec3) (ε : ℝ) : Vec3 → Vec3 := fun y => ε ^ 2 • X (ε • y)

theorem Xsc_contDiff (hX : ContDiff ℝ 3 X) (ε : ℝ) : ContDiff ℝ 3 (Xsc X ε) :=
  by
  unfold Xsc
  have h : ContDiff ℝ 3 (fun y : Vec3 => X (ε • y)) :=
    hX.comp (contDiff_id.const_smul ε)
  exact h.const_smul (ε ^ 2)

theorem fderiv_Xsc (hX : ContDiff ℝ 3 X) (ε : ℝ) (y : Vec3) :
    fderiv ℝ (Xsc X ε) y = (ε ^ 2 * ε) • fderiv ℝ X (ε • y) :=
  fderiv_scale (ε ^ 2) ε ((hX.differentiable (by norm_num)) _)

theorem vecLap_Xsc (hX : ContDiff ℝ 3 X) (ε : ℝ) (y : Vec3) :
    vecLap (Xsc X ε) y = ε ^ 4 • vecLap X (ε • y) := by
  unfold vecLap
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hg : Differentiable ℝ (fun w => fderiv ℝ X w (Pi.single j 1 : Vec3)) := fun w =>
    ((apply_hasFDeriv hX w _).differentiableAt)
  have e : (fun y' => fderiv ℝ (Xsc X ε) y' (Pi.single j 1 : Vec3)) =
      fun y' => (ε ^ 2 * ε) • (fun w => fderiv ℝ X w (Pi.single j 1 : Vec3)) (ε • y') := by
    funext y'; rw [fderiv_Xsc hX]; rfl
  rw [e, fderiv_scale _ ε (hg _)]
  simp only [ContinuousLinearMap.smul_apply, smul_smul]
  congr 1

theorem fderiv_vecLap_Xsc (hX : ContDiff ℝ 3 X) (ε : ℝ) (y : Vec3) :
    fderiv ℝ (vecLap (Xsc X ε)) y = ε ^ 5 • fderiv ℝ (vecLap X) (ε • y) := by
  have e : vecLap (Xsc X ε) = fun y' => ε ^ 4 • vecLap X (ε • y') := funext (vecLap_Xsc hX ε)
  rw [e, fderiv_scale _ ε ((vecLap_diff hX) _)]
  congr 1

theorem smul_gam {ε : ℝ} (hε : 0 < ε) (s : ℝ) : ε • gam ε s = gam 1 s := by
  have hεne : ε ≠ 0 := hε.ne'
  ext k
  fin_cases k <;> simp [gam] <;> field_simp

end JetClockCore

/-- `ClockEps1`: the `ε = 1` degree `-7` kernel bound for `D_yΔ_yX^mt` on the ray
(source 4917-4937, 5449-5458): `|D_yΔ_yX^mt(R/√s,0,0)| ≤ P_ν s^{7/2} N` for `0 < s ≤ 1/ν`,
`N = N₁(χ_oM)` (`IIIa.firstMoment`), uniformly for `μ ∈ K`. -/
def ClockEps1At (K : Set ℝ) (χo χy : ℝ → ℝ) (C : ℝ) (k : ℕ) : Prop :=
  ∀ (ν μ : ℝ), LHyp (cOf ν) ν 1 μ χo χy → μ ∈ K →
    ∀ M : Chart → Mat3, OldThinFinite (cOf ν) ν M → ∀ s ∈ Ioc (0 : ℝ) (1 / ν),
      ENNReal.ofReal (frob (fun i j => fderiv ℝ (vecLap (Xmt (cOf ν) ν 1 μ χo χy M))
          (JetClockCore.gam 1 s) (Pi.single j 1) i)) ≤
        ENNReal.ofReal (C * ν⁻¹ ^ k * s ^ (7 / 2 : ℝ)) *
          UnforcedLeray.Short.IIIa.firstMoment (cOf ν) 0 (fun p => χo (ν * p.1) • M p)

def ClockEps1 (K : Set ℝ) (χo χy : ℝ → ℝ) : Prop := ∃ (C : ℝ) (k : ℕ), ClockEps1At K χo χy C k

theorem rj7_frob_smul (a : ℝ) (A : Mat3) : frob (a • A) = |a| * frob A := by
  unfold frob
  have : ∀ i j, (a • A) i j ^ 2 = a ^ 2 * A i j ^ 2 := fun i j => by
    simp [Pi.smul_apply, mul_pow]
  simp only [this, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-! ## The kernel input, reduced to three lemmas (source 4870-4937, 5449-5458) -/

/-- The cut old moment `∫_{u>1.2/ν} u^{-3/2} χ_o(νu) ⨍|M|` (source 4924-4927, 5400). -/
def oldN0cut (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) : ℝ :=
  ∫ u in Ioi (6 / 5 / ν), u ^ (-(3 / 2 : ℝ)) *
    (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))

/-- **Lemma 1 (Newton field on the receiver region, cut moment)** (source 4776-4782, 4870-4900):
`V_{μ,M}` is `C^7` on `{|w|² > 11ν/12}` with `‖∂^mV(w)‖ ≤ C_m N₀^χ(M)|w|^{-4-m}`, `m ≤ 7`. -/
def NewtonVCutBound (χo : ℝ → ℝ) : Prop :=
  ∃ C : ℕ → ℝ, ∀ (c ν μ : ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo → 0 ≤ μ →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ContDiffOn ℝ 7 (newtonV c ν μ χo M) {w | ν * (11 / 12) < eucSq w} ∧
      ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
        ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w‖ ≤
          C m * oldN0cut c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)

/-- **Lemma 2 (stream cutoff, third derivative)** (source 4917-4937, 5449-5458): for `Z` as in
`StreamCutJet`, `|D_yΔ_y(𝒞_yZ)(s^{-1/2},0,0)| ≤ C₀ B s^{7/2}` for `0 < s ≤ 1/ν` (each of the three
derivatives costs `r^{-1}`; `D_yX = O(B s^{5/2})`). -/
def StreamCutThird (χy : ℝ → ℝ) : Prop :=
  ∃ C0 : ℝ, ∀ (ν B : ℝ), 0 < ν → 0 ≤ B → ∀ Z : Vec3 → Vec3,
    ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w} →
    (∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤ B * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) →
    IsStreamCutoff χy →
    ∀ s ∈ Ioc (0 : ℝ) (1 / ν),
      frob (fun i j => fderiv ℝ (vecLap (streamCut ν 1 χy Z)) (JetClockCore.gam 1 s)
        (Pi.single j 1) i) ≤ C0 * B * s ^ (7 / 2 : ℝ)

/-- **Lemma 3 (cut moment against `N₁`)** (source 5400; `IIIa.firstMoment`): Cauchy-Schwarz in `q`
and `1 + |η|/√s ≥ 1`; `χ_o(νs) = 0` for `s ≤ 1.2/ν`. -/
def N0cutLeN1 : Prop :=
  ∀ (c ν : ℝ) (χo : ℝ → ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ENNReal.ofReal (oldN0cut c ν χo M) ≤
        UnforcedLeray.Short.IIIa.firstMoment c 0 (fun p => χo (ν * p.1) • M p)

theorem oldN0cut_nonneg (c ν : ℝ) (hν : 0 < ν) {χo : ℝ → ℝ} (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) : 0 ≤ oldN0cut c ν χo M := by
  unfold oldN0cut
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hu0 : 0 < u := ha.trans hu
  exact mul_nonneg (Real.rpow_nonneg hu0.le _)
    (mul_nonneg (hχ.range _).1 (integral_nonneg fun x => Real.sqrt_nonneg _))

theorem clockEps1_of {K : Set ℝ} {χo χy : ℝ → ℝ} (hV : NewtonVCutBound χo)
    (hS : StreamCutThird χy) (hN : N0cutLeN1) : ClockEps1 K χo χy := by
  obtain ⟨C, hC⟩ := hV
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨|C0| * ∑ m ∈ Finset.range 8, (|C m| + |C m|), 0, ?_⟩
  intro ν μ h _ M hM s hs
  have hN0 := oldN0cut_nonneg (cOf ν) ν h.nu_pos h.chiO M
  have hmu0 : 0 ≤ μ := h.mu_pos.le
  have hmu1 : 0 ≤ μ + 1 := by linarith
  obtain ⟨h1, h1b⟩ := hC (cOf ν) ν μ h.c_pos h.nu_pos h.chiO hmu0 M hM
  obtain ⟨h2, h2b⟩ := hC (cOf ν) ν (μ + 1) h.c_pos h.nu_pos h.chiO hmu1 M hM
  have hY : ∀ μ' : ℝ, youngW (cOf ν) ν 1 μ' χo M = newtonV (cOf ν) ν μ' χo M := by
    intro μ'; funext y; simp [youngW]
  set S : ℝ := ∑ m ∈ Finset.range 8, (|C m| + |C m|) with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun m _ => by positivity
  set Z : Vec3 → Vec3 := newtonV (cOf ν) ν μ χo M - newtonV (cOf ν) ν (μ + 1) χo M with hZ
  have hopen : IsOpen {w : Vec3 | ν * (11 / 12) < eucSq w} := by
    unfold eucSq
    exact isOpen_lt continuous_const (by fun_prop)
  have hZs : ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w} := h1.sub h2
  have hZb : ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤
        (S * oldN0cut (cOf ν) ν χo M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
    intro m hm w hw
    have hat1 : ContDiffAt ℝ 7 (newtonV (cOf ν) ν μ χo M) w := h1.contDiffAt (hopen.mem_nhds hw)
    have hat2 : ContDiffAt ℝ 7 (newtonV (cOf ν) ν (μ + 1) χo M) w :=
      h2.contDiffAt (hopen.mem_nhds hw)
    have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
    rw [hZ, iteratedFDeriv_sub_apply (hat1.of_le hmle) (hat2.of_le hmle)]
    have hp : 0 ≤ (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hb1 := h1b m hm w hw
    have hb2 := h2b m hm w hw
    have hSm : |C m| + |C m| ≤ S :=
      Finset.single_le_sum (f := fun m => |C m| + |C m|) (fun m _ => by positivity)
        (Finset.mem_range.2 (by omega))
    have hCm : C m + C m ≤ S := le_trans (add_le_add (le_abs_self _) (le_abs_self _)) hSm
    calc ‖iteratedFDeriv ℝ m (newtonV (cOf ν) ν μ χo M) w -
            iteratedFDeriv ℝ m (newtonV (cOf ν) ν (μ + 1) χo M) w‖
        ≤ ‖iteratedFDeriv ℝ m (newtonV (cOf ν) ν μ χo M) w‖ +
            ‖iteratedFDeriv ℝ m (newtonV (cOf ν) ν (μ + 1) χo M) w‖ := norm_sub_le _ _
      _ ≤ C m * oldN0cut (cOf ν) ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) +
          C m * oldN0cut (cOf ν) ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) :=
          add_le_add hb1 hb2
      _ = (C m + C m) * (oldN0cut (cOf ν) ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) := by
          ring
      _ ≤ S * (oldN0cut (cOf ν) ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) :=
          mul_le_mul_of_nonneg_right hCm (mul_nonneg hN0 hp)
      _ = (S * oldN0cut (cOf ν) ν χo M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by ring
  have hL : Xmt (cOf ν) ν 1 μ χo χy M = streamCut ν 1 χy Z := by
    funext y'
    simp only [Xmt, hY, hZ]
  rw [hL]
  have key := hC0 ν (S * oldN0cut (cOf ν) ν χo M) h.nu_pos (mul_nonneg hSnn hN0) Z hZs hZb
    h.chiY s hs
  have hspos : 0 < s := hs.1
  have hpow : 0 ≤ s ^ (7 / 2 : ℝ) := Real.rpow_nonneg hspos.le _
  have hcoef : 0 ≤ |C0| * S * ν⁻¹ ^ 0 * s ^ (7 / 2 : ℝ) := by simp only [pow_zero, mul_one]; positivity
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal (|C0| * S * ν⁻¹ ^ 0 * s ^ (7 / 2 : ℝ) *
          oldN0cut (cOf ν) ν χo M) := by
        apply ENNReal.ofReal_le_ofReal
        have : C0 * (S * oldN0cut (cOf ν) ν χo M) * s ^ (7 / 2 : ℝ) ≤
            |C0| * S * ν⁻¹ ^ 0 * s ^ (7 / 2 : ℝ) * oldN0cut (cOf ν) ν χo M := by
          simp only [pow_zero, mul_one]
          have h3 : 0 ≤ S * oldN0cut (cOf ν) ν χo M * s ^ (7 / 2 : ℝ) := by positivity
          nlinarith [le_abs_self C0]
        linarith
    _ = ENNReal.ofReal (|C0| * S * ν⁻¹ ^ 0 * s ^ (7 / 2 : ℝ)) *
          ENNReal.ofReal (oldN0cut (cOf ν) ν χo M) := ENNReal.ofReal_mul hcoef
    _ ≤ _ := by
        gcongr
        exact hN (cOf ν) ν χo h.c_pos h.nu_pos h.chiO M hM

/-- One regime. -/
theorem rj7_jetClockAt (Pl : UnforcedLeray.Blueprint.Planar.PlanarData) (K : ReturnConsts)
    (L : ReturnLevel) (μ : ℝ) (Kset : Set ℝ) (hμK : μ ∈ Kset) (hν1 : L.ν ≤ 1) (hμ0 : 0 < μ)
    (hμ1 : μ < 1 / 4) (hmZ : 3 / 2 < K.mZ) (hγ : 0 < gRate Pl) (hχy : IsStreamCutoff K.χy)
    (hχf : IsSourceCutoffC K.χf) {C1 : ℝ} {k1 : ℕ} (hC : ClockEps1At Kset K.χo K.χy C1 k1) :
    JetClockAt Pl K L μ |C1| k1 := by
  intro T s hs
  obtain ⟨CN, kN, hCN⟩ := sourceLN0 K.mZ (gRate Pl) hmZ hγ
  have hfin : OldThinFinite (cOf L.ν) L.ν (thinRep T) :=
    (hCN (cOf L.ν) L.ν (L.ρb Pl K) (cOf_pos L.ν_pos) L.ν_pos hν1 T).1
  have hL1 : LHyp (cOf L.ν) L.ν 1 μ K.χo K.χy :=
    ⟨cOf_pos L.ν_pos, L.ν_pos, hν1, one_pos, hμ0, hμ1, K.hχo, hχy⟩
  have hLε : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy :=
    ⟨cOf_pos L.ν_pos, L.ν_pos, hν1, L.ε_pos, hμ0, hμ1, K.hχo, hχy⟩
  have hX : ContDiff ℝ 3 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)) :=
    (xmtSmooth _ _ _ _ _ _ hLε _ hfin).of_le (by norm_num)
  have hX1 : ContDiff ℝ 3 (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy (thinRep T)) :=
    (xmtSmooth _ _ _ _ _ _ hL1 _ hfin).of_le (by norm_num)
  have hspos : 0 < s := hs.1
  have hay := ay_LjFun_of (sourceLYoung (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy)
    hχf hLε hmZ hγ T
  have hA : LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T =
      JetClockCore.Af (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)) L.ε := by
    funext s'
    unfold LjFun Lpt JetClockCore.Af JetClockCore.gam
    rfl
  have hid : Bmat L.ν μ K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
      s = Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) s +
        clockJet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) s := by
    unfold Bmat
    rw [hay, hA]
    exact JetClockCore.clock_identity hX L.ε L.ν μ hspos
  refine ⟨hid, ?_⟩
  rw [hid, add_sub_cancel_left]
  have hXe : Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) =
      JetClockCore.Xsc (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy (thinRep T)) L.ε :=
    Scale.Xmt_smul L.ε_pos
  have hcl : clockJet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) s =
      (L.ν / s * L.ε ^ 5) • (fun i j => fderiv ℝ (vecLap (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy
        (thinRep T))) (JetClockCore.gam 1 s) (Pi.single j 1) i) := by
    funext i j
    unfold clockJet
    rw [hXe, JetClockCore.fderiv_vecLap_Xsc hX1 L.ε]
    have : (![L.ε⁻¹ / Real.sqrt s, 0, 0] : Vec3) = JetClockCore.gam L.ε s := rfl
    rw [this, JetClockCore.smul_gam L.ε_pos s]
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hcl, rj7_frob_smul]
  have hcpos : 0 ≤ L.ν / s * L.ε ^ 5 := by
    have := L.ν_pos; have := L.ε_pos; positivity
  rw [abs_of_nonneg hcpos, ENNReal.ofReal_mul hcpos]
  have h1 := hC L.ν μ hL1 hμK (thinRep T) hfin s hs
  have hs72 : s ^ (7 / 2 : ℝ) = s * s ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' hspos.le (by norm_num)]; norm_num
  have hkpos : 0 ≤ L.ν⁻¹ ^ k1 := by have := L.ν_pos; positivity
  have hspow : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hspos.le _
  have hreal : L.ν / s * L.ε ^ 5 * (C1 * L.ν⁻¹ ^ k1 * s ^ (7 / 2 : ℝ)) ≤
      |C1| * L.ν⁻¹ ^ k1 * L.ν * L.ε ^ 5 * s ^ (5 / 2 : ℝ) := by
    have e : L.ν / s * L.ε ^ 5 * (C1 * L.ν⁻¹ ^ k1 * s ^ (7 / 2 : ℝ)) =
        C1 * L.ν⁻¹ ^ k1 * L.ν * L.ε ^ 5 * s ^ (5 / 2 : ℝ) := by
      rw [hs72]; field_simp
    rw [e]
    have : 0 ≤ L.ν⁻¹ ^ k1 * L.ν * L.ε ^ 5 * s ^ (5 / 2 : ℝ) := by
      have := L.ν_pos; have := L.ε_pos; positivity
    nlinarith [le_abs_self C1]
  calc ENNReal.ofReal (L.ν / s * L.ε ^ 5) * ENNReal.ofReal (frob fun i j => fderiv ℝ
          (vecLap (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy (thinRep T))) (JetClockCore.gam 1 s)
          (Pi.single j 1) i)
      ≤ ENNReal.ofReal (L.ν / s * L.ε ^ 5) * (ENNReal.ofReal (C1 * L.ν⁻¹ ^ k1 * s ^ (7 / 2 : ℝ)) *
          oldN1 Pl K L T) := by
        gcongr
        exact h1
    _ = ENNReal.ofReal (L.ν / s * L.ε ^ 5 * (C1 * L.ν⁻¹ ^ k1 * s ^ (7 / 2 : ℝ))) *
          oldN1 Pl K L T := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hcpos]
    _ ≤ _ := by gcongr

/-- **The sequence statement from the `ε = 1` clock bound.** -/
theorem jetClock_ofClock (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : ClockEps1 (Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2)) D.K.χo D.K.χy) : D.JetClock := by
  obtain ⟨C1, k1, hC⟩ := h1
  refine ⟨|C1|, k1, ?_⟩
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (Iic_mem_nhds one_pos)
  filter_upwards [mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt, hν]
    with n hmu hn z hz
  have hm := hmu z hz
  have h0 := hst.sigma_pos
  have h1' := hst.sigma_lt
  exact rj7_jetClockAt D.Pl D.K (D.level n) (D.mu n z) _ hm hn (by linarith [hm.1])
    (by linarith [hm.2]) hst.mZ_gt hst.gamma_pos hst.chiY hst.chiF hC

/-- **`jetClock` from the three kernel lemmas.** -/
theorem jetClock_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : NewtonVCutBound D.K.χo) (h2 : StreamCutThird D.K.χy) (h3 : N0cutLeN1) : D.JetClock :=
  jetClock_ofClock D hst (clockEps1_of h1 h2 h3)

end UnforcedLeray.Short.PartIIIb.Concrete
