import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.Defs

/-!
# `YBPhase.sepX0OscFar0` (task `PartIII-b:C/rep/8/1/1/2/5/1/1/2`)

Source `the November 2 reference manuscript`
lines 5400-5427, SP 3768-3790.

Proves `YBPhase.SepX0OscFar0`: order-`0` phase-primitive oscillation bound for `X₀` on the
transition annulus `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4`, mirroring `GeomX/PhasePrimitive/FarLeaf.lean`
and `GeomX/PhasePrimitive/FarLeafOrg/{Point,Pointwise}.lean` one spatial derivative lower (for
`sepW` itself rather than `fderiv sepW`, using `D1` in place of `Hk`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray UnforcedLeray.Short.IIIa
open UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

namespace YBPhase

open YBComm PhasePrim

/-! ## 1. Kernel bounds for `D1` (order-`0` analogue of `kerPack`) -/

private lemma pack0_B1 (C0 : ℝ)
    (h0 : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ t : ℝ, 0 < t →
      ‖iteratedFDeriv ℝ (0 + 1) (fun y => heatLerayK t i k y) x‖ ≤ C0 * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)))
    (i j k : Fin 3) {s : ℝ} (hs : 0 < s) (x : Space) (hx : x ≠ 0) :
    ‖D1 i j k (s, x)‖ ≤ |C0| * ‖x‖ ^ (-4 : ℝ) := by
  rw [D1_eq i j k hs x]
  have c := h0 x hx i j s hs
  have e : (-4 - ((0 : ℕ) : ℝ)) = -4 := by norm_num
  rw [e] at c
  have hp : 0 ≤ ‖x‖ ^ (-4 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have c' : ‖fderiv ℝ (fun y => heatLerayK s i j y) x‖ ≤ |C0| * ‖x‖ ^ (-4 : ℝ) := by
    rw [nrm_one]
    exact c.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)
  calc ‖fderiv ℝ (fun x' => heatLerayK s i j x') x (UnforcedLeray.coordinateVector k)‖
      ≤ ‖fderiv ℝ (fun x' => heatLerayK s i j x') x‖ * ‖UnforcedLeray.coordinateVector k‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fun x' => heatLerayK s i j x') x‖ := by rw [ek_norm k, mul_one]
    _ ≤ |C0| * ‖x‖ ^ (-4 : ℝ) := c'

private lemma pack0_B2 (Cd : ℝ)
    (hd : ∀ (i j k : Fin 3) (t : ℝ), 0 < t → ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ 0 (fun y => deriv (fun s => fderiv ℝ (fun x' => heatLerayK s i j x') y
        (UnforcedLeray.coordinateVector k)) t) x‖ ≤ Cd * ‖x‖ ^ (-6 - ((0 : ℕ) : ℝ)))
    (i j k : Fin 3) {s : ℝ} (hs : 0 < s) (x : Space) (hx : x ≠ 0) :
    ‖fderiv ℝ (D1 i j k) (s, x) ((1 : ℝ), (0 : Space))‖ ≤ |Cd| * ‖x‖ ^ (-6 : ℝ) := by
  have hEq : (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') x
      (UnforcedLeray.coordinateVector k)) =ᶠ[𝓝 s] fun s' => D1 i j k (s', x) := by
    filter_upwards [(isOpen_Ioi (a := (0 : ℝ))).mem_nhds hs] with s' hs'
    exact (D1_eq i j k hs' x).symm
  have h1 : HasDerivAt (fun s' : ℝ => ((s', x) : ℝ × Space)) ((1 : ℝ), (0 : Space)) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
  have hg : deriv (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') x
      (UnforcedLeray.coordinateVector k)) s =
      fderiv ℝ (D1 i j k) (s, x) ((1 : ℝ), (0 : Space)) := by
    rw [hEq.deriv_eq]
    exact ((D1_d i j k (p := (s, x)) hs).hasFDerivAt.comp_hasDerivAt s h1).deriv
  rw [← hg]
  have hb := hd i j k s hs x hx
  rw [norm_iteratedFDeriv_zero] at hb
  have e : (-6 - ((0 : ℕ) : ℝ)) = -6 := by norm_num
  rw [e] at hb
  have hp : 0 ≤ ‖x‖ ^ (-6 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)

private theorem kerPack0 : ∃ C : ℝ, 0 < C ∧ ∀ (i j k : Fin 3) (s : ℝ), 0 < s →
    ∀ x : Space, x ≠ 0 → ∀ v : Space,
      ‖D1 i j k (s, x)‖ ≤ C * ‖x‖ ^ (-4 : ℝ) ∧
      ‖fderiv ℝ (D1 i j k) (s, x) ((1 : ℝ), (0 : Space))‖ ≤ C * ‖x‖ ^ (-6 : ℝ) ∧
      ‖fderiv ℝ (D1 i j k) (s, x) ((0 : ℝ), v)‖ ≤ C * ‖v‖ * ‖x‖ ^ (-5 : ℝ) := by
  obtain ⟨C0, hC0⟩ := sepKernelBounds 0
  obtain ⟨C1, hC1⟩ := sepKernelBounds 1
  obtain ⟨Cd, _, hCd⟩ := farKerDt
  refine ⟨|C0| + |C1| + |Cd| + 1, by positivity, ?_⟩
  intro i j k s hs x hx v
  have b1 := pack0_B1 C0 (fun x hx i k t ht => (hC0 x hx i k).1 t ht) i j k hs x hx
  have b2 := pack0_B2 Cd (fun i j k t ht x hx => hCd i j k t ht x hx 0 (Nat.zero_le 1))
    i j k hs x hx
  have b3 : ‖fderiv ℝ (D1 i j k) (s, x) ((0 : ℝ), v)‖ ≤ |C1| * ‖v‖ * ‖x‖ ^ (-5 : ℝ) :=
    pack_B1 C1 (fun x hx i k t ht => (hC1 x hx i k).1 t ht) i j k hs x hx v
  have hv := norm_nonneg v
  have p4 : 0 ≤ ‖x‖ ^ (-4 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have p5 : 0 ≤ ‖x‖ ^ (-5 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have p6 : 0 ≤ ‖x‖ ^ (-6 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨b1.trans ?_, b2.trans ?_, b3.trans ?_⟩
  · nlinarith [abs_nonneg C0, abs_nonneg C1, abs_nonneg Cd]
  · nlinarith [abs_nonneg C0, abs_nonneg C1, abs_nonneg Cd]
  · nlinarith [mul_nonneg hv p5, abs_nonneg C0, abs_nonneg C1, abs_nonneg Cd]

/-! ## 2. Phase coefficient `om0` and single-point oscillation estimate -/

private def om0 (a : ℂ) (ν : ℝ) (z y0 : Space) (i j k : Fin 3) (l : ℝ) : ℂ :=
  (l : ℂ) ^ a * ((D1 i j k (pth ν z y0 l) : ℝ) : ℂ)

private lemma om0_cd {ν : ℝ} (hν : 0 < ν) (a : ℂ) (z y0 : Space) (i j k : Fin 3) :
    ContDiffOn ℝ 1 (om0 a ν z y0 i j k) (Ioo 0 1) := by
  have hpath : ContDiff ℝ 1 (pth ν z y0) := by
    unfold pth
    exact (contDiff_const.mul (contDiff_const.sub (contDiff_id.pow 2))).prodMk
      (contDiff_const.sub (contDiff_id.smul contDiff_const))
  have hD1 : ContDiffOn ℝ 1 (D1 i j k) {p : ℝ × Space | 0 < p.1} :=
    (D1_cd i j k).of_le (by norm_num)
  have h1 : ContDiffOn ℝ 1 (fun l => D1 i j k (pth ν z y0 l)) (Ioo 0 1) :=
    hD1.comp hpath.contDiffOn (fun l hl => pth_pos' hν z y0 hl)
  have h2 : ContDiffOn ℝ 1 (fun l => ((D1 i j k (pth ν z y0 l) : ℝ) : ℂ)) (Ioo 0 1) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h1
  exact (cpow_cd a).mul h2

private lemma om0_form {ν : ℝ} (hν : 0 < ν) (a : ℂ) (z y0 : Space) (i j k : Fin 3) {l : ℝ}
    (hl : l ∈ Ioo (0 : ℝ) 1) :
    om0 a ν z y0 i j k l + (l : ℂ) * deriv (om0 a ν z y0 i j k) l =
      ((1 + a) * (l : ℂ) ^ a) * ((D1 i j k (pth ν z y0 l) : ℝ) : ℂ) +
      ((l : ℂ) * (l : ℂ) ^ a) *
        ((fderiv ℝ (D1 i j k) (pth ν z y0 l) (-(2 * ν * l), -z) : ℝ) : ℂ) := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.1.ne'
  have hslit : (l : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simpa using hl.1
  have hc : HasDerivAt (fun l : ℝ => (l : ℂ) ^ a) (a * (l : ℂ) ^ (a - 1)) l :=
    ((Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt).comp_ofReal
  have hh : HasDerivAt (fun l => D1 i j k (pth ν z y0 l))
      (fderiv ℝ (D1 i j k) (pth ν z y0 l) (-(2 * ν * l), -z)) l :=
    (D1_d i j k (pth_pos' hν z y0 hl)).hasFDerivAt.comp_hasDerivAt l (pth_hasDeriv ν z y0 l)
  have hm := hc.mul hh.ofReal_comp
  have hderiv : deriv (om0 a ν z y0 i j k) l = _ := hm.deriv
  rw [hderiv]
  have e : (l : ℂ) ^ (a - 1) = (l : ℂ) ^ a / l := by
    rw [Complex.cpow_sub _ _ hl0, Complex.cpow_one]
  rw [e]
  unfold om0
  field_simp
  ring

private lemma om0_bounds (C : ℝ) (hC0 : 0 ≤ C)
    (hpk : ∀ (i j k : Fin 3) (s : ℝ), 0 < s → ∀ x : Space, x ≠ 0 → ∀ v : Space,
      ‖D1 i j k (s, x)‖ ≤ C * ‖x‖ ^ (-4 : ℝ) ∧
      ‖fderiv ℝ (D1 i j k) (s, x) ((1 : ℝ), (0 : Space))‖ ≤ C * ‖x‖ ^ (-6 : ℝ) ∧
      ‖fderiv ℝ (D1 i j k) (s, x) ((0 : ℝ), v)‖ ≤ C * ‖v‖ * ‖x‖ ^ (-5 : ℝ))
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (a : ℂ) (z y0 : Space) (i j k : Fin 3)
    {g Z : ℝ} (hg : 0 < g) (hZ : ‖z‖ ≤ Z)
    (hgap : ∀ l ∈ Ioo (0 : ℝ) 1, g ≤ ‖y0 - l • z‖) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    ‖om0 a ν z y0 i j k l‖ ≤ l ^ a.re * (C * g ^ (-4 : ℝ)) ∧
    ‖om0 a ν z y0 i j k l + (l : ℂ) * deriv (om0 a ν z y0 i j k) l‖ ≤
      l ^ a.re * (‖1 + a‖ * (C * g ^ (-4 : ℝ)) + 2 * C * g ^ (-6 : ℝ) + C * Z * g ^ (-5 : ℝ)) := by
  have hx : y0 - l • z ≠ 0 := by
    intro h0; have := hgap l hl; rw [h0, norm_zero] at this; linarith
  have hs : 0 < ν * (1 - l ^ 2) := pth_pos' hν z y0 hl
  obtain ⟨b1, b2, b3⟩ := hpk i j k _ hs _ hx (-z)
  have hxg : g ≤ ‖y0 - l • z‖ := hgap l hl
  have r4 : ‖y0 - l • z‖ ^ (-4 : ℝ) ≤ g ^ (-4 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by norm_num)
  have r5 : ‖y0 - l • z‖ ^ (-5 : ℝ) ≤ g ^ (-5 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by norm_num)
  have r6 : ‖y0 - l • z‖ ^ (-6 : ℝ) ≤ g ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by norm_num)
  have hh : |D1 i j k (pth ν z y0 l)| ≤ C * g ^ (-4 : ℝ) := by
    rw [← Real.norm_eq_abs]
    exact b1.trans (mul_le_mul_of_nonneg_left r4 hC0)
  have hp : pth ν z y0 l = (ν * (1 - l ^ 2), y0 - l • z) := rfl
  have hdec : (-(2 * ν * l), -z) = (-(2 * ν * l)) • ((1 : ℝ), (0 : Space)) + ((0 : ℝ), -z) := by
    ext <;> simp
  have hh' : |fderiv ℝ (D1 i j k) (pth ν z y0 l) (-(2 * ν * l), -z)| ≤
      2 * C * g ^ (-6 : ℝ) + C * Z * g ^ (-5 : ℝ) := by
    rw [← Real.norm_eq_abs, hdec, map_add, map_smul, hp]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [smul_eq_mul, norm_mul]
      have e1 : ‖-(2 * ν * l)‖ ≤ 2 := by
        rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by have := hl.1; positivity)]
        nlinarith [hl.1, hl.2]
      calc _ ≤ 2 * (C * ‖y0 - l • z‖ ^ (-6 : ℝ)) :=
            mul_le_mul e1 b2 (norm_nonneg _) (by norm_num)
        _ ≤ 2 * (C * g ^ (-6 : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r6 hC0) (by norm_num)
        _ = _ := by ring
    · refine b3.trans ?_
      rw [norm_neg]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hZ hC0) r5
        (Real.rpow_nonneg (norm_nonneg _) _)
        (by have := (norm_nonneg z).trans hZ; positivity)
  have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
  refine ⟨?_, ?_⟩
  · unfold om0
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hh hlr
  · rw [om0_form hν a z y0 i j k hl]
    refine (norm_add_le _ _).trans ?_
    have n1 : ‖((1 + a) * (l : ℂ) ^ a) * ((D1 i j k (pth ν z y0 l) : ℝ) : ℂ)‖ ≤
        l ^ a.re * (‖1 + a‖ * (C * g ^ (-4 : ℝ))) := by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real,
        Real.norm_eq_abs]
      calc ‖1 + a‖ * l ^ a.re * |D1 i j k (pth ν z y0 l)|
          ≤ ‖1 + a‖ * l ^ a.re * (C * g ^ (-4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
        _ = _ := by ring
    have n2 : ‖((l : ℂ) * (l : ℂ) ^ a) *
        ((fderiv ℝ (D1 i j k) (pth ν z y0 l) (-(2 * ν * l), -z) : ℝ) : ℂ)‖ ≤
        l ^ a.re * (2 * C * g ^ (-6 : ℝ) + C * Z * g ^ (-5 : ℝ)) := by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl.1]
      calc l * l ^ a.re * |fderiv ℝ (D1 i j k) (pth ν z y0 l) (-(2 * ν * l), -z)|
          ≤ 1 * l ^ a.re * (2 * C * g ^ (-6 : ℝ) + C * Z * g ^ (-5 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hl.2.le hlr) hh' (abs_nonneg _) (by positivity)
        _ = _ := by ring
    linarith

private theorem oscPoint0 :
    ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧
      ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
        ∀ f : ℝ → ℝ, Measurable f → (∀ q, f (q + c) = f q) → (∫ q in Ioc 0 c, f q) = 0 →
        ∀ (z xo : Space) (q₀ : ℝ), ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ ρo →
          ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ (i j k : Fin 3),
            ‖∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
                ((fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)
                  (ε⁻¹ • xo - l • z) (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) *
                ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)‖ₑ ≤
              ENNReal.ofReal ((Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) / ε) *
                (C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ m * ε ^ 6 *
                  (1 + |z 2|) * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ))) *
                ∫⁻ q in Ioc 0 c, ‖f q‖ₑ := by
  intro K hK hRe
  obtain ⟨C, hCpos, hpk⟩ := kerPack0
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set Λ : ℝ := 3 + 2 * |R|
  have hΛ1 : 1 ≤ Λ := by linarith [abs_nonneg R]
  refine ⟨(2 * Λ + 8) * C, 9, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ f hfm hper hmean z xo q₀ hz hxo i j k
  set r : ℝ := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hrpos : 0 < r := lt_of_lt_of_le hρi hxo
  have hd : 0 < r - ρo := by linarith
  set y0 : Space := ε⁻¹ • xo
  set g : ℝ := (r - ρo) / ε
  have hg : 0 < g := div_pos hd hε
  set Z : ℝ := ρo / ε + |z 2|
  have hzh : hor z ≤ ρo / ε := by
    rw [le_div_iff₀ hε, mul_comm]; exact hz
  have hZ : ‖z‖ ≤ Z := by linarith [norm_le_hor z]
  have hZ0 : 0 ≤ Z := (norm_nonneg z).trans hZ
  have hgap : ∀ l ∈ Ioo (0 : ℝ) 1, g ≤ ‖y0 - l • z‖ := by
    intro l hl
    have h1 := hor_sub y0 z l hl.1.le
    have h2 : hor y0 = ε⁻¹ * r := by
      rw [hor_smul _ (inv_nonneg.2 hε.le)]; rfl
    have h3 : l * hor z ≤ ρo / ε := by
      calc l * hor z ≤ 1 * (ρo / ε) :=
            mul_le_mul hl.2.le hzh (by unfold hor; positivity) (by norm_num)
        _ = _ := one_mul _
    have h4 : g = ε⁻¹ * r - ρo / ε := by unfold g; field_simp
    have := hor_le_norm (y0 - l • z)
    linarith
  set a : ℂ := 2 * μ + 2
  have hare : a.re = 2 * μ.re + 2 := by simp [a]
  have hμre := hRe μ hμ
  have hnorm : ‖1 + a‖ ≤ Λ := by
    calc ‖1 + (2 * μ + 2)‖ = ‖(3 : ℂ) + 2 * μ‖ := by congr 1; ring
      _ ≤ ‖(3 : ℂ)‖ + ‖2 * μ‖ := norm_add_le _ _
      _ ≤ 3 + 2 * |R| := by
        rw [norm_mul]
        have h3 : ‖(3 : ℂ)‖ = 3 := by simp
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h3, h2]
        have := hR μ hμ
        have := le_abs_self R
        linarith
  set E0 : ℝ := Λ * (C * g ^ (-4 : ℝ)) + 2 * C * g ^ (-6 : ℝ) + C * Z * g ^ (-5 : ℝ)
  have g4 : 0 < g ^ (-4 : ℝ) := Real.rpow_pos_of_pos hg _
  have g5 : 0 ≤ g ^ (-5 : ℝ) := Real.rpow_nonneg hg.le _
  have g6 : 0 < g ^ (-6 : ℝ) := Real.rpow_pos_of_pos hg _
  have hE0 : 0 < E0 := by positivity
  have hb := fun l (hl : l ∈ Ioo (0 : ℝ) 1) =>
    om0_bounds C hCpos.le hpk hν hν1 a z y0 i j k hg hZ hgap hl
  have hkey := osc_abstract phaseIBP (om0 a ν z y0 i j k) (a.re + 1) E0
    (by rw [hare]; linarith) hE0 (om0_cd hν a z y0 i j k)
    (fun l hl => by
      have := (hb l hl).1
      have e : a.re + 1 - 1 = a.re := by ring
      rw [e]
      refine this.trans ?_
      have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
      rw [mul_comm E0]
      refine mul_le_mul_of_nonneg_left ?_ hlr
      have : 0 ≤ C * g ^ (-4 : ℝ) := by positivity
      nlinarith [mul_nonneg this (by linarith : 0 ≤ Λ - 1), mul_pos hCpos g6,
        mul_nonneg (mul_nonneg hCpos.le hZ0) g5])
    (fun l hl => by
      have := (hb l hl).2
      have e : a.re + 1 - 1 = a.re := by ring
      rw [e]
      refine this.trans ?_
      have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
      rw [mul_comm E0]
      refine mul_le_mul_of_nonneg_left ?_ hlr
      have : 0 ≤ C * g ^ (-4 : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hnorm this])
    ε c hε hc f hfm hper hmean q₀
  have hint_eq : (∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
      ((fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)
        (y0 - l • z) (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) *
      ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)) =
      ∫ l in Ioo (0 : ℝ) 1, om0 a ν z y0 i j k l *
        ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
    have hs : 0 < ν * (1 - l ^ 2) := pth_pos' hν z y0 hl
    unfold om0 pth
    rw [D1_eq i j k hs (y0 - l • z)]
  rw [hint_eq]
  refine hkey.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hg45 : g ^ (-4 : ℝ) = g * g ^ (-5 : ℝ) := by
    rw [mul_comm, ← Real.rpow_add_one hg.ne']; norm_num
  have hg56 : g ^ (-5 : ℝ) = g * g ^ (-6 : ℝ) := by
    rw [mul_comm, ← Real.rpow_add_one hg.ne']; norm_num
  have hg67 : g ^ (-6 : ℝ) = g * g ^ (-7 : ℝ) := by
    rw [mul_comm, ← Real.rpow_add_one hg.ne']; norm_num
  set E : ℝ := Λ * (C * g ^ (-5 : ℝ)) + 2 * C * g ^ (-7 : ℝ) + C * Z * g ^ (-6 : ℝ)
  have hE_pos : 0 ≤ 2 * ε * E := by
    have : 0 ≤ g ^ (-7 : ℝ) := Real.rpow_nonneg hg.le _
    positivity
  have hE0_eq : 2 * ε * E0 = g * (2 * ε * E) := by
    unfold E0 E
    rw [hg45, hg56, hg67]
    ring
  have hg_le : g ≤ r / ε := div_le_div_of_nonneg_right (by linarith) hε.le
  have hrp := real_part C Λ ε ρo ρi ν c r (z 2) hCpos hΛ1 hν hc hε hε1 hρo hρ hxo hg
  calc 2 * ε * E0 = g * (2 * ε * E) := hE0_eq
    _ ≤ (r / ε) * ((2 * Λ + 8) * C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ 9 * ε ^ 6 *
          (1 + |z 2|) * r ^ (-5 : ℝ)) :=
        mul_le_mul hg_le hrp hE_pos (div_nonneg hrpos.le hε.le)

/-! ## 3. Pointwise bound for `sepW` of a zero-mean thin source (`oscFarPt0`) -/

private lemma pi_enorm_le {v : Fin 3 → ℂ} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h : ∀ i : Fin 3, ‖v i‖ₑ ≤ M) : ‖v‖ₑ ≤ M := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_toReal hM]
  refine ENNReal.ofReal_le_ofReal ((pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2 fun i => ?_)
  have hi := h i
  rw [← ofReal_norm_eq_enorm] at hi
  exact (ENNReal.ofReal_le_iff_le_toReal hM).1 hi

private lemma sepDiffF_sum_entryF_apply (ν ε : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (p : ℝ × Space) (y0 : Space) :
    sepDiffF ν μ (thinSource ε F) τ p y0 =
      ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0 := by
  rw [sepDiffF_sum_entryF]
  simp only [Finset.sum_apply]

set_option maxHeartbeats 800000 in
private theorem oscFarPt0 :
    ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
        ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
          (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
          (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
          (∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
          (∀ x' Y i j, ∫ q in Ioc 0 c, F x' Y q i j = 0) →
          IIIa.thinMoment c F ≠ ⊤ →
          ∀ xo : Space, ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ τ : ℝ,
            ENNReal.ofReal (ε * (Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2))⁻¹) *
                ‖sepW ν μ (thinSource ε F) (ε⁻¹ • xo) τ‖ₑ ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ k * ε ^ 4 *
                  Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c F := by
  intro K hK hRe
  obtain ⟨C₀, m, hC₀, hOsc⟩ := oscPoint0 K hK hRe
  refine ⟨18 * C₀, m + 1, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ F hmeas hper hsupp hzero hN xo hxo τ
  have hth : ThinHyp c ρo F := ⟨hmeas, hper, hsupp⟩
  set y0 : Space := ε⁻¹ • xo
  set r : ℝ := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  set B : ℝ := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hrpos : 0 < r := lt_of_lt_of_le hρi hxo
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := mul_nonneg hρi.le (inv_nonneg.2 (by linarith))
    positivity
  have hcB : c ≤ B := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := mul_nonneg hρi.le (inv_nonneg.2 (by linarith))
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have : 0 ≤ ρi⁻¹ := inv_nonneg.2 hρi.le
    change c ≤ 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
    linarith
  have hy0 : ρi / ε ≤ Real.sqrt (y0 0 ^ 2 + y0 1 ^ 2) := by
    change ρi / ε ≤ hor (ε⁻¹ • xo)
    rw [hor_smul _ (inv_nonneg.2 hε.le), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  have hP : 0 < 2 * ε * c := by positivity
  have hDomF : sepDom (2 * μ.re + 2) 0 (ρi / ε - ρo / ε) (srcNorm (thinSource ε F)) τ y0 < ⊤ :=
    sepDom_thin_lt_top hε hc hρ (hRe μ hμ) hth hN τ y0
  obtain ⟨hIntF, hEqF⟩ := (IIIa.t17s_local IIIa.sepKernelBounds ν hν μ (ρo / ε) (ρi / ε)
    (2 * ε * c) (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) (thinSource ε F)
    (thin_isSep hε hth) τ y0 hy0 hDomF).1.self_of_nhds
  have hIntE : ∀ j₀ k₀ : Fin 3,
      Integrable (fun p => sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0) sepDiffRho := by
    intro j₀ k₀
    have hNE : IIIa.thinMoment c (entryF j₀ k₀ F) ≠ ⊤ :=
      ne_top_of_le_ne_top hN (thinMoment_entryF_le c F j₀ k₀)
    have hDomE := sepDom_thin_lt_top hε hc hρ (hRe μ hμ) (thinHyp_entryF hth j₀ k₀) hNE τ y0
    exact (IIIa.t17s_local IIIa.sepKernelBounds ν hν μ (ρo / ε) (ρi / ε) (2 * ε * c)
      (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) (thinSource ε (entryF j₀ k₀ F))
      (thin_isSep hε (thinHyp_entryF hth j₀ k₀)) τ y0 hy0 hDomE).1.self_of_nhds.1
  have hEntryBound : ∀ (j₀ k₀ i : Fin 3),
      ‖(∫ p, sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0 ∂sepDiffRho) i‖ₑ ≤
        ENNReal.ofReal ((r / ε) * (2 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
          IIIa.thinMoment c F := by
    intro j₀ k₀ i
    let Λ : (Fin 3 → ℂ) →L[ℝ] ℂ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i
    have hΛInt : Integrable (fun p =>
        sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0 i) sepDiffRho :=
      Λ.integrable_comp (hIntE j₀ k₀)
    have hΛEq : (∫ p, sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0 ∂sepDiffRho) i =
        ∫ z : Space, ∫ l in Ioo (0 : ℝ) 1,
          sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z) y0 i := by
      have h1 := (Λ.integral_comp_comm (hIntE j₀ k₀)).symm
      simp only [Λ, ContinuousLinearMap.proj_apply] at h1
      rw [h1]
      exact integral_prod_symm _ hΛInt
    rw [hΛEq]
    have hSlice : ∀ z : Space,
        ‖∫ l in Ioo (0 : ℝ) 1,
            sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z) y0 i‖ₑ ≤
          ENNReal.ofReal ((r / ε) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ))) *
            (ENNReal.ofReal (1 + |z 2|) *
              ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) := by
      intro z
      have hcongr : (∫ l in Ioo (0 : ℝ) 1,
          sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z) y0 i) =
          (-2 : ℂ) * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
            ((fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j₀ x)
              (y0 - l • z) (UnforcedLeray.coordinateVector k₀) : ℝ) : ℂ) *
            ((F (ε * z 0, ε * z 1) (z 2) (q0 ε τ z + ε⁻¹ * Real.log l) j₀ k₀ : ℝ) : ℂ) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun l _ => ?_
        rw [sepDiffF_entryF ν ε μ F τ j₀ k₀ (l, z) y0 i,
          thinSource_q0_apply hε F τ l z j₀ k₀]
        ring
      rw [hcongr, enorm_mul]
      have h2 : ‖(-2 : ℂ)‖ₑ = ENNReal.ofReal 2 := by
        rw [← ofReal_norm_eq_enorm]; norm_num
      rw [h2]
      by_cases hz : ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ ρo
      · have hfm : Measurable (fun q => F (ε * z 0, ε * z 1) (z 2) q j₀ k₀) :=
          (hmeas j₀ k₀).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
        have hpt := hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ
          (fun q => F (ε * z 0, ε * z 1) (z 2) q j₀ k₀) hfm
          (fun q => by rw [hper]) (hzero (ε * z 0, ε * z 1) (z 2) j₀ k₀)
          z xo (q0 ε τ z) hz hxo i j₀ k₀
        have hle_q : (∫⁻ q in Ioc 0 c, ‖F (ε * z 0, ε * z 1) (z 2) q j₀ k₀‖ₑ) ≤
            ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) := by
          refine lintegral_mono fun q => ?_
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (l5_abs_le_tensorNorm _ j₀ k₀)
        calc ENNReal.ofReal 2 * _
            ≤ ENNReal.ofReal 2 *
                (ENNReal.ofReal ((r / ε) * (C₀ * B ^ m * ε ^ 6 * (1 + |z 2|) * r ^ (-5 : ℝ))) *
                  ∫⁻ q in Ioc 0 c,
                    ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) :=
              mul_le_mul_right (hpt.trans (mul_le_mul_right hle_q _)) _
          _ = _ := by
              have hpos1 : 0 ≤ (r / ε) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) := by positivity
              have heq : ENNReal.ofReal 2 *
                  ENNReal.ofReal ((r / ε) * (C₀ * B ^ m * ε ^ 6 * (1 + |z 2|) * r ^ (-5 : ℝ))) =
                  ENNReal.ofReal ((r / ε) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ))) *
                    ENNReal.ofReal (1 + |z 2|) := by
                rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hpos1]
                congr 1; ring
              rw [← mul_assoc, heq, mul_assoc]
      · push Not at hz
        have hF0 : ∀ q, F (ε * z 0, ε * z 1) (z 2) q = 0 := by
          intro q
          apply hsupp
          have : Real.sqrt ((ε * z 0) ^ 2 + (ε * z 1) ^ 2) =
              ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
            rw [show (ε * z 0) ^ 2 + (ε * z 1) ^ 2 = ε ^ 2 * (z 0 ^ 2 + z 1 ^ 2) by ring,
              Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]
          rw [this]; exact hz
        simp [hF0]
    calc ‖∫ z : Space, ∫ l in Ioo (0 : ℝ) 1,
            sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z) y0 i‖ₑ
        ≤ ∫⁻ z : Space, ‖∫ l in Ioo (0 : ℝ) 1,
            sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z) y0 i‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z : Space,
            ENNReal.ofReal ((r / ε) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ))) *
              (ENNReal.ofReal (1 + |z 2|) *
                ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) :=
          lintegral_mono hSlice
      _ = ENNReal.ofReal ((r / ε) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ))) *
            ∫⁻ z : Space, ENNReal.ofReal (1 + |z 2|) *
              ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((r / ε) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ))) *
            (ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * IIIa.thinMoment c F)) :=
          mul_le_mul_right (thin_z_moment_le hε hc hth) _
      _ ≤ ENNReal.ofReal ((r / ε) * (2 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
            IIIa.thinMoment c F := by
          rw [← mul_assoc, ← mul_assoc]
          refine mul_le_mul_left ?_ _
          rw [← ENNReal.ofReal_pow (inv_nonneg.2 hε.le),
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hε6 : ε ^ 6 * (ε⁻¹) ^ 2 = ε ^ 4 := by
            have : ε ≠ 0 := hε.ne'
            field_simp
          have h1 : (r / ε) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) * (ε⁻¹) ^ 2 * c =
              (r / ε) * (2 * C₀ * (B ^ m * c) * ε ^ 4 * r ^ (-5 : ℝ)) := by
            calc (r / ε) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) * (ε⁻¹) ^ 2 * c
                = (r / ε) * (2 * C₀ * B ^ m * (ε ^ 6 * (ε⁻¹) ^ 2) * r ^ (-5 : ℝ) * c) := by ring
              _ = (r / ε) * (2 * C₀ * (B ^ m * c) * ε ^ 4 * r ^ (-5 : ℝ)) := by rw [hε6]; ring
          have hBm : B ^ m * c ≤ B ^ (m + 1) := by
            rw [pow_succ]
            exact mul_le_mul_of_nonneg_left hcB (pow_nonneg hB0 m)
          rw [h1]
          gcongr
  rw [hEqF]
  have hSumInt : (∫ p, sepDiffF ν μ (thinSource ε F) τ p y0 ∂sepDiffRho) =
      ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        ∫ p, sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0 ∂sepDiffRho := by
    have hcongr : (fun p => sepDiffF ν μ (thinSource ε F) τ p y0) =
        fun p => ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
          sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0 :=
      funext fun p => sepDiffF_sum_entryF_apply ν ε μ F τ p y0
    rw [hcongr,
      integral_finset_sum _ fun j₀ _ => integrable_finset_sum _ fun k₀ _ => hIntE j₀ k₀]
    refine Finset.sum_congr rfl fun j₀ _ => ?_
    exact integral_finset_sum _ fun k₀ _ => hIntE j₀ k₀
  rw [hSumInt]
  have hM_ne_top :
      ENNReal.ofReal ((r / ε) * (18 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
        IIIa.thinMoment c F ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
  have hNormLe :
      ‖∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
          ∫ p, sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0 ∂sepDiffRho‖ₑ ≤
        ENNReal.ofReal ((r / ε) * (18 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
          IIIa.thinMoment c F := by
    refine pi_enorm_le hM_ne_top fun i => ?_
    simp only [Finset.sum_apply]
    calc ‖∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
            (∫ p, sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0 ∂sepDiffRho) i‖ₑ
        ≤ ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
            ‖(∫ p, sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0 ∂sepDiffRho) i‖ₑ :=
          (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j₀ _ => enorm_sum_le _ _)
      _ ≤ ∑ _j₀ : Fin 3, ∑ _k₀ : Fin 3,
            ENNReal.ofReal ((r / ε) * (2 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
              IIIa.thinMoment c F :=
          Finset.sum_le_sum fun j₀ _ => Finset.sum_le_sum fun k₀ _ => hEntryBound j₀ k₀ i
      _ = ENNReal.ofReal ((r / ε) * (18 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
            IIIa.thinMoment c F := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← mul_assoc, ← mul_assoc]
          congr 1
          have h3 : ((3 : ℕ) : ℝ≥0∞) * ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 9 := by norm_num
          rw [h3, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  calc ENNReal.ofReal (ε * r⁻¹) *
        ‖∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
          ∫ p, sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y0 ∂sepDiffRho‖ₑ
      ≤ ENNReal.ofReal (ε * r⁻¹) *
          (ENNReal.ofReal ((r / ε) * (18 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
            IIIa.thinMoment c F) :=
        mul_le_mul_right hNormLe _
    _ = ENNReal.ofReal (18 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        have hε0 : ε ≠ 0 := hε.ne'
        have hr0 : r ≠ 0 := hrpos.ne'
        field_simp

/-! ## 4. Splitting `sepW` and assembling `YBPhase.sepX0OscFar0` -/

private lemma sepDiffF_thin_split0 (ν ε c : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (p : ℝ × Space) :
    sepDiffF ν μ (thinSource ε F) τ p =
      sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p +
        sepDiffF ν μ (thinSource ε (perpPart c F)) τ p := by
  ext y' i
  have hthin : ∀ σ z, thinSource ε F σ z =
      thinSource ε (meanLift (IIIa.phaseMean c F)) σ z + thinSource ε (perpPart c F) σ z := by
    intro σ z
    unfold thinSource meanLift perpPart
    simp
  simp only [sepDiffF, Pi.add_apply, hthin]
  simp only [Matrix.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

private lemma sepW_thin_split {ν c ε ρo ρi : ℝ} {μ : ℂ}
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hρo : 0 ≤ ρo) (hρ : ρo < ρi)
    (hμ : -(1 / 4) < μ.re) {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hth : ThinHyp c ρo F) (hth1 : ThinHyp c ρo (meanLift (IIIa.phaseMean c F)))
    (hth2 : ThinHyp c ρo (perpPart c F))
    (hN : IIIa.thinMoment c F ≠ ⊤) (hN1 : IIIa.thinMoment c (meanLift (IIIa.phaseMean c F)) ≠ ⊤)
    (hN2 : IIIa.thinMoment c (perpPart c F) ≠ ⊤)
    {xo : Space} (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (τ : ℝ) :
    sepW ν μ (thinSource ε F) (ε⁻¹ • xo) τ -
        sepW ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) (ε⁻¹ • xo) τ =
      sepW ν μ (thinSource ε (perpPart c F)) (ε⁻¹ • xo) τ := by
  set y0 : Space := ε⁻¹ • xo
  have hy0 : ρi / ε ≤ Real.sqrt (y0 0 ^ 2 + y0 1 ^ 2) := by
    change ρi / ε ≤ hor (ε⁻¹ • xo)
    rw [hor_smul _ (inv_nonneg.2 hε.le), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  obtain ⟨hInt0, hEq0⟩ := (IIIa.t17s_local IIIa.sepKernelBounds ν hν μ (ρo / ε) (ρi / ε)
    (2 * ε * c) (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) (thinSource ε F)
    (thin_isSep hε hth) τ y0 hy0 (sepDom_thin_lt_top hε hc hρ hμ hth hN τ y0)).1.self_of_nhds
  obtain ⟨hInt1, hEq1⟩ := (IIIa.t17s_local IIIa.sepKernelBounds ν hν μ (ρo / ε) (ρi / ε)
    (2 * ε * c) (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε)
    (thinSource ε (meanLift (IIIa.phaseMean c F)))
    (thin_isSep hε hth1) τ y0 hy0 (sepDom_thin_lt_top hε hc hρ hμ hth1 hN1 τ y0)).1.self_of_nhds
  obtain ⟨hInt2, hEq2⟩ := (IIIa.t17s_local IIIa.sepKernelBounds ν hν μ (ρo / ε) (ρi / ε)
    (2 * ε * c) (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε)
    (thinSource ε (perpPart c F))
    (thin_isSep hε hth2) τ y0 hy0 (sepDom_thin_lt_top hε hc hρ hμ hth2 hN2 τ y0)).1.self_of_nhds
  rw [hEq0, hEq1, hEq2]
  have hcongr : (fun p => sepDiffF ν μ (thinSource ε F) τ p y0) =
      fun p => sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p y0 +
        sepDiffF ν μ (thinSource ε (perpPart c F)) τ p y0 :=
    funext fun p => congrFun (sepDiffF_thin_split0 ν ε c μ F τ p) y0
  rw [hcongr, integral_add hInt1 hInt2, add_sub_cancel_left]

private theorem srcX0_sub_le (ν μ : ℝ) (src src' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (y : Space) :
    ‖srcX0 ν μ src τ y - srcX0 ν μ src' τ y‖ ≤
      2 * (‖IIIa.sepW ν (μ : ℂ) src y τ - IIIa.sepW ν (μ : ℂ) src' y τ‖ +
          ‖IIIa.sepW ν ((μ : ℂ) + 1) src y τ - IIIa.sepW ν ((μ : ℂ) + 1) src' y τ‖) := by
  have hw : ∀ s, srcX0 ν μ s τ y =
      PhasePrim.reMap (IIIa.sepW ν (μ : ℂ) s y τ - IIIa.sepW ν ((μ : ℂ) + 1) s y τ) :=
    fun _ => rfl
  rw [hw src, hw src', ← map_sub]
  set a := IIIa.sepW ν (μ : ℂ) src y τ
  set b := IIIa.sepW ν ((μ : ℂ) + 1) src y τ
  set a' := IIIa.sepW ν (μ : ℂ) src' y τ
  set b' := IIIa.sepW ν ((μ : ℂ) + 1) src' y τ
  have e : a - b - (a' - b') = (a - a') - (b - b') := by abel
  rw [e]
  calc ‖PhasePrim.reMap ((a - a') - (b - b'))‖
      ≤ ‖PhasePrim.reMap‖ * ‖(a - a') - (b - b')‖ := PhasePrim.reMap.le_opNorm _
    _ ≤ 2 * (‖a - a'‖ + ‖b - b'‖) :=
        mul_le_mul PhasePrim.opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)

private theorem poly_le_13_0 (ν c : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c) :
    1 + ν⁻¹ + c + (Real.sqrt ν)⁻¹ +
        Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 13 * (1 + ν⁻¹ + c) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hg := PhasePrim.gap_le ν hν
  have hd : 0 < Real.sqrt ν - Real.sqrt (5 * ν / 6) := by linarith
  have h1 : Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 12 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hd]
    linarith
  have hνi : 1 ≤ ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have hsν : ν ≤ Real.sqrt ν := by
    have := Real.sqrt_le_sqrt (mul_le_of_le_one_left hν.le hν1 : ν * ν ≤ ν)
    rwa [Real.sqrt_mul_self hν.le] at this
  have h3 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hsν
  linarith

/-- **Sub-leaf 2 (`SepX0OscFar0`)**: order-`0` phase-primitive oscillation bound for `X₀` on the
transition annulus `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4` (source 5400-5427, SP 3768-3790). -/
theorem sepX0OscFar0 : SepX0OscFar0 := by
  obtain ⟨C₀, k₀, hC₀, hOsc⟩ := oscFarPt0 PhasePrim.Kmu PhasePrim.Kmu_compact PhasePrim.Kmu_re
  refine ⟨8 * C₀ * 13 ^ k₀, k₀, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx _
  set ρo := Real.sqrt (5 * ν / 6)
  set ρi := Real.sqrt ν
  have hρo : 0 ≤ ρo := Real.sqrt_nonneg _
  have hρ : ρo < ρi := Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hρi_xo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := Real.sqrt_le_sqrt hνx
  have hμK : ((μ : ℝ) : ℂ) ∈ PhasePrim.Kmu := ⟨μ, ⟨hμ0.le, by linarith⟩, rfl⟩
  have hμ1K : ((μ : ℂ) + 1) ∈ PhasePrim.Kmu :=
    ⟨μ + 1, ⟨by linarith, by linarith⟩, by push_cast; rfl⟩
  have hth : ThinHyp c ρo F := ⟨hFm, hFp, hFs⟩
  obtain ⟨hm1, hm2⟩ := IIIa.sepMomentSplit c hc F hFm
  have hN1 : IIIa.thinMoment c (IIIa.meanLift (IIIa.phaseMean c F)) ≠ ⊤ :=
    ne_top_of_le_ne_top hFfin hm1
  have hN2 : IIIa.thinMoment c (IIIa.perpPart c F) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hFfin) hm2
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.phaseMean c F w.1 w.2 i j :=
    IIIa.phaseMean_measurable c F hFm
  have hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → IIIa.phaseMean c F x' Y = 0 := by
    intro x' Y h
    funext i j
    simp [IIIa.phaseMean, hFs x' Y _ h]
  have hth1 : ThinHyp c ρo (IIIa.meanLift (IIIa.phaseMean c F)) :=
    ⟨fun i j => (hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop),
     fun _ _ _ => rfl,
     fun x' Y _ h => hGs x' Y h⟩
  have hth2 : ThinHyp c ρo (IIIa.perpPart c F) :=
    ⟨fun i j => (hFm i j).sub
       ((hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop)),
     fun x' Y q => by simp [IIIa.perpPart, hFp],
     fun x' Y q h => by simp [IIIa.perpPart, hFs x' Y q h, hGs x' Y h]⟩
  set b := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  set M := 1 + ν⁻¹ + c
  set r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hr0 : 0 < r := lt_of_lt_of_le (Real.sqrt_pos.2 hν) hρi_xo
  have hb0 : 0 ≤ b := by
    have : 0 < ρi - ρo := sub_pos.2 hρ
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := by positivity
    positivity
  have hM0 : 0 ≤ M := by positivity
  have hble : b ^ k₀ ≤ 13 ^ k₀ * M ^ k₀ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hb0 (poly_le_13_0 ν c hν hν1 hc) k₀
  set a : ℝ≥0∞ :=
    ENNReal.ofReal (8 * C₀ * 13 ^ k₀ * M ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F
  refine ⟨fun _ => a, measurable_const, fun _ => rfl, ?_, ?_⟩
  · refine Eventually.of_forall fun τ => ?_
    have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
    have hreμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
    have hsp0 := sepW_thin_split hν hc hε hρo hρ hreμ hth hth1 hth2 hFfin hN1 hN2 hρi_xo τ
    have hsp1 := sepW_thin_split hν hc hε hρo hρ hreμ1 hth hth1 hth2 hFfin hN1 hN2 hρi_xo τ
    have hd := srcX0_sub_le ν μ (IIIa.thinSource ε F)
      (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ (ε⁻¹ • xo)
    rw [hsp0, hsp1] at hd
    have hpt0 := (hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ (μ : ℂ) hμK (IIIa.perpPart c F)
      hth2.meas hth2.per hth2.supp (IIIa.perpPart_meanZero c hc F) hN2 xo hρi_xo τ).trans
      (mul_le_mul_right hm2 _)
    have hpt1 := (hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ ((μ : ℂ) + 1) hμ1K (IIIa.perpPart c F)
      hth2.meas hth2.per hth2.supp (IIIa.perpPart_meanZero c hc F) hN2 xo hρi_xo τ).trans
      (mul_le_mul_right hm2 _)
    set w0 := ‖IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε (IIIa.perpPart c F)) (ε⁻¹ • xo) τ‖ₑ
    set w1 := ‖IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε (IIIa.perpPart c F)) (ε⁻¹ • xo) τ‖ₑ
    have hle1 : ENNReal.ofReal (ε * r⁻¹) *
        ‖srcX0 ν μ (IIIa.thinSource ε F) τ (ε⁻¹ • xo) -
          srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ (ε⁻¹ • xo)‖ₑ ≤
        ENNReal.ofReal 2 * (ENNReal.ofReal (ε * r⁻¹) * w0 + ENNReal.ofReal (ε * r⁻¹) * w1) := by
      rw [← ofReal_norm]
      calc ENNReal.ofReal (ε * r⁻¹) * ENNReal.ofReal _
          ≤ ENNReal.ofReal (ε * r⁻¹) * ENNReal.ofReal (2 * (‖IIIa.sepW ν (μ : ℂ)
              (IIIa.thinSource ε (IIIa.perpPart c F)) (ε⁻¹ • xo) τ‖ +
              ‖IIIa.sepW ν ((μ : ℂ) + 1)
                (IIIa.thinSource ε (IIIa.perpPart c F)) (ε⁻¹ • xo) τ‖)) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal hd) _
        _ = ENNReal.ofReal 2 *
              (ENNReal.ofReal (ε * r⁻¹) * w0 + ENNReal.ofReal (ε * r⁻¹) * w1) := by
            rw [ENNReal.ofReal_mul (p := 2) (by norm_num),
              ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm]
            ring
    refine hle1.trans ?_
    calc ENNReal.ofReal 2 * (ENNReal.ofReal (ε * r⁻¹) * w0 + ENNReal.ofReal (ε * r⁻¹) * w1)
        ≤ ENNReal.ofReal 2 *
            (ENNReal.ofReal (C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ)) * (2 * IIIa.thinMoment c F) +
              ENNReal.ofReal (C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ)) * (2 * IIIa.thinMoment c F)) := by
          gcongr
      _ = ENNReal.ofReal (8 * C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F := by
          have hc0 : 0 ≤ C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) := by positivity
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
          rw [← two_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, h2,
            ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
      _ ≤ a := by
          unfold a
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          have hr5 : 0 ≤ r ^ (-5 : ℝ) := Real.rpow_nonneg hr0.le _
          calc 8 * C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ)
              = 8 * C₀ * b ^ k₀ * (ε ^ 4 * r ^ (-5 : ℝ)) := by ring
            _ ≤ 8 * C₀ * (13 ^ k₀ * M ^ k₀) * (ε ^ 4 * r ^ (-5 : ℝ)) := by gcongr
            _ = 8 * C₀ * 13 ^ k₀ * M ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) := by ring
  · have hP : 0 < 2 * ε * c := by positivity
    exact (IIIa.ltauAt_const (2 * ε * c) hP a).le

end YBPhase

end UnforcedLeray.Short.PartIIIb.Concrete
end
