import UnforcedLeray.Short.PartIIIb.NearInst.Body.Forced

/-!
# The geometric body column (source 4119-4122, 3962-3969, 4011-4020): proof of `BodyGeomColumn`

`w = (R_ε - R_0) f = 1_{below} w + 1_{above} w + 1_{tail} w + 1_{box} w`, the box being
`binSet ε^a ε^{-b} L_⊥`.  On the three complementary regions the train bounds
(`IIIa.RawCoeffEarly`, `IIIa.RawCoeffLate`, `IIIa.RawTransverseTail`, `Delta.RawStreamCompletion`)
and `Delta.TrainMultRestr` bound `‖G⁻¹M_0 1_A w‖` by `2B‖w‖`, `‖w‖ ≤ 8‖f‖`; on the box
`FlatTrainMultBound` with `Delta.TrainMultRestr` on `univ` and `BodyWindowComparison`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile)

/-! ## The four-piece partition of the output -/

theorem ind_four (sm S L : ℝ) (hsmS : sm ≤ S) (x : Chart) :
    Delta.ind (Delta.ageBelow sm) x + Delta.ind (Delta.ageAbove S) x +
      Delta.ind (Delta.tailSet sm S L) x + Delta.ind (Delta.binSet sm S L) x = 1 := by
  unfold Delta.ind Delta.ageBelow Delta.ageAbove Delta.tailSet Delta.binSet
  by_cases h1 : x.1 < sm
  · have h2 : ¬ S ≤ x.1 := by intro h; linarith
    have h3 : ¬ (sm ≤ x.1) := by intro h; linarith
    simp [Set.indicator, h1, h2, h3]
  · by_cases h2 : S ≤ x.1
    · have h3 : ¬ x.1 < S := by
        intro h
        have : sm ≤ x.1 := not_lt.1 h1
        have : x.1 < S := h
        linarith
      simp [Set.indicator, h1, h2, h3]
    · have h3 : x.1 < S := not_le.1 h2
      have h4 : sm ≤ x.1 := not_lt.1 h1
      by_cases h5 : L < |x.2.2|
      · have h6 : ¬ |x.2.2| ≤ L := not_le.2 h5
        simp [Set.indicator, h1, h2, h3, h4, h5, h6]
      · have h6 : |x.2.2| ≤ L := not_lt.1 h5
        simp [Set.indicator, h1, h2, h3, h4, h5, h6]

theorem outRestr_four (c sm S L : ℝ) (hsmS : sm ≤ S) (u : Hsp c) :
    Delta.outRestr c (Delta.ageBelow sm) u + Delta.outRestr c (Delta.ageAbove S) u +
      Delta.outRestr c (Delta.tailSet sm S L) u + Delta.outRestr c (Delta.binSet sm S L) u = u := by
  have h1 := Delta.measurableSet_ageBelow sm
  have h2 := Delta.measurableSet_ageAbove S
  have h3 := Delta.measurableSet_tailSet sm S L
  have h4 := Delta.measurableSet_binSet sm S L
  apply Lp.ext
  have e1 := Delta.restrLp_ae (μ := ageμ c (-3 / 2)) (E := EuclideanSpace ℝ (Fin 2)) h1 u
  have e2 := Delta.restrLp_ae (μ := ageμ c (-3 / 2)) (E := EuclideanSpace ℝ (Fin 2)) h2 u
  have e3 := Delta.restrLp_ae (μ := ageμ c (-3 / 2)) (E := EuclideanSpace ℝ (Fin 2)) h3 u
  have e4 := Delta.restrLp_ae (μ := ageμ c (-3 / 2)) (E := EuclideanSpace ℝ (Fin 2)) h4 u
  filter_upwards [Lp.coeFn_add (Delta.outRestr c (Delta.ageBelow sm) u +
      Delta.outRestr c (Delta.ageAbove S) u + Delta.outRestr c (Delta.tailSet sm S L) u)
      (Delta.outRestr c (Delta.binSet sm S L) u),
    Lp.coeFn_add (Delta.outRestr c (Delta.ageBelow sm) u + Delta.outRestr c (Delta.ageAbove S) u)
      (Delta.outRestr c (Delta.tailSet sm S L) u),
    Lp.coeFn_add (Delta.outRestr c (Delta.ageBelow sm) u) (Delta.outRestr c (Delta.ageAbove S) u),
    e1, e2, e3, e4] with x a1 a2 a3 b1 b2 b3 b4
  rw [a1, Pi.add_apply, a2, Pi.add_apply, a3, Pi.add_apply]
  change _ = (u : Chart → EuclideanSpace ℝ (Fin 2)) x
  have hb1 : (Delta.outRestr c (Delta.ageBelow sm) u : Chart → _) x =
      Delta.ind (Delta.ageBelow sm) x • (u : Chart → _) x := b1
  have hb2 : (Delta.outRestr c (Delta.ageAbove S) u : Chart → _) x =
      Delta.ind (Delta.ageAbove S) x • (u : Chart → _) x := b2
  have hb3 : (Delta.outRestr c (Delta.tailSet sm S L) u : Chart → _) x =
      Delta.ind (Delta.tailSet sm S L) x • (u : Chart → _) x := b3
  have hb4 : (Delta.outRestr c (Delta.binSet sm S L) u : Chart → _) x =
      Delta.ind (Delta.binSet sm S L) x • (u : Chart → _) x := b4
  rw [hb1, hb2, hb3, hb4, ← add_smul, ← add_smul, ← add_smul, ind_four sm S L hsmS, one_smul]

/-! ## One region of the output -/

theorem piece_region (hG : GainInvContract) (hM1 : Delta.TrainMultRestr) {c mZ ρb γ ν : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hγ : 0 ≤ γ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (M0 : Hsp c →L[ℝ] Zsp c mZ ρb) (hM0 : IsFlatMult M0 tr) (A : Set Chart)
    (hA : MeasurableSet A) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ p ∈ A, 0 < p.1 →
      Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p * ‖trainMer tr p‖ ≤ B)
    (u : Hsp c) :
    ‖(gainEquiv c mZ ρb γ hν).symm (M0 (Delta.outRestr c A u))‖ ≤ 2 * B * ‖u‖ := by
  have hM := hM1 c mZ ρb γ ν hν tr M0 A B hc hA hB0 hM0 hB
  have hkey : Delta.gainRestrM γ hν A M0 ((gainH c γ hν).symm u) =
      (gainEquiv c mZ ρb γ hν).symm (M0 (Delta.outRestr c A u)) := by
    rw [Delta.gainRestrM, Delta.gainConjM_apply]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hGI : ‖(gainH c γ hν).symm u‖ ≤ ‖u‖ := (hG c mZ ρb γ ν hν hγ).1 u
  rw [← hkey]
  calc ‖Delta.gainRestrM γ hν A M0 ((gainH c γ hν).symm u)‖
      ≤ ‖Delta.gainRestrM γ hν A M0‖ * ‖(gainH c γ hν).symm u‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 2 * B * ‖u‖ :=
        mul_le_mul hM hGI (norm_nonneg _) (by linarith)

/-- The four-region bound of `‖G⁻¹ M_0 w‖` (source 3962-3969, 4011-4020). -/
theorem geom_split (hG : GainInvContract) (hM1 : Delta.TrainMultRestr) {c mZ ρb γ ν : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hγ : 0 ≤ γ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (M0 : Hsp c →L[ℝ] Zsp c mZ ρb) (hM0 : IsFlatMult M0 tr) (sm S L : ℝ) (hsmS : sm ≤ S)
    (Bb Ba Bt Bf : ℝ) (hBb : 0 ≤ Bb) (hBa : 0 ≤ Ba) (hBt : 0 ≤ Bt) (hBf : 0 ≤ Bf)
    (hb : ∀ p ∈ Delta.ageBelow sm, 0 < p.1 →
      Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p * ‖trainMer tr p‖ ≤ Bb)
    (ha : ∀ p ∈ Delta.ageAbove S, 0 < p.1 →
      Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p * ‖trainMer tr p‖ ≤ Ba)
    (ht : ∀ p ∈ Delta.tailSet sm S L, 0 < p.1 →
      Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p * ‖trainMer tr p‖ ≤ Bt)
    (hf : ∀ p ∈ (univ : Set Chart), 0 < p.1 →
      Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p * ‖trainMer tr p‖ ≤ Bf)
    (w : Hsp c) :
    ‖(gainEquiv c mZ ρb γ hν).symm (M0 w)‖ ≤
      2 * Bb * ‖w‖ + 2 * Ba * ‖w‖ + 2 * Bt * ‖w‖ +
        2 * Bf * ‖Delta.outRestr c (Delta.binSet sm S L) w‖ := by
  have e := outRestr_four c sm S L hsmS w
  have p1 := piece_region hG hM1 hν hc hγ tr M0 hM0 _ (Delta.measurableSet_ageBelow sm) Bb hBb hb w
  have p2 := piece_region hG hM1 hν hc hγ tr M0 hM0 _ (Delta.measurableSet_ageAbove S) Ba hBa ha w
  have p3 := piece_region hG hM1 hν hc hγ tr M0 hM0 _ (Delta.measurableSet_tailSet sm S L) Bt hBt ht w
  have p4 := piece_region hG hM1 hν hc hγ tr M0 hM0 univ MeasurableSet.univ Bf hBf hf
    (Delta.outRestr c (Delta.binSet sm S L) w)
  rw [Delta.outRestr_univ_apply] at p4
  conv_lhs => rw [← e]
  simp only [map_add]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add p1 p2)) p3)) p4)

/-! ## Numerical bookkeeping (copies of `Delta.up`, `Delta.up1`, `Delta.exists_pos_le_list`) -/

theorem exists_pos_le_list' : ∀ l : List ℝ, (∀ x ∈ l, 0 < x) → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ x ∈ l, ν₀ ≤ x
  | [], _ => ⟨1, one_pos, by simp⟩
  | x :: l, h => by
    obtain ⟨m, hm, hle⟩ := exists_pos_le_list' l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨min x m, lt_min (h x (by simp)) hm, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hle y hy)

theorem up' {x C t X Q c : ℝ} {k kk : ℕ} (h : x ≤ C * X ^ k * t) (hX : 1 ≤ X) (hk : k ≤ kk)
    (ht : 0 ≤ t) (hc : max C 0 ≤ c) (hQ : Q = X ^ kk) : x ≤ c * Q * t := by
  have h1 : C * X ^ k ≤ c * X ^ kk :=
    mul_le_mul ((le_max_left C 0).trans hc) (pow_le_pow_right₀ hX hk)
      (pow_nonneg (by linarith) _) ((le_max_right C 0).trans hc)
  rw [hQ]
  exact h.trans (mul_le_mul_of_nonneg_right h1 ht)

theorem up1' {x C X Q c : ℝ} {k kk : ℕ} (h : x ≤ C * X ^ k) (hX : 1 ≤ X) (hk : k ≤ kk)
    (hc : max C 0 ≤ c) (hQ : Q = X ^ kk) : x ≤ c * Q := by
  rw [hQ]
  exact h.trans (mul_le_mul ((le_max_left C 0).trans hc) (pow_le_pow_right₀ hX hk)
    (pow_nonneg (by linarith) _) ((le_max_right C 0).trans hc))

theorem regime_facts'' {p : Params} {d dm dp : ℝ} (h : UnforcedLeray.Short.IIb.BgRegime p d dm dp) :
    p.ε < 1 ∧ Real.log p.ε = -d / p.ν := by
  have hd : 0 < d := lt_of_lt_of_le h.dm_pos h.dm_le
  have hν := p.ν_pos
  refine ⟨?_, ?_⟩
  · rw [h.eps_eq, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by linarith) hν
  · rw [h.eps_eq, Real.log_exp]

theorem transWeight_nonneg' (mZ : ℝ) (p : Chart) :
    0 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  positivity

/-! ## The train bounds on the output regions (source 3962-3969, 4011-4020) -/

theorem train_bounds (hFT : FlatTrainMultBound) (hSC : Delta.RawStreamCompletion)
    (hRE : UnforcedLeray.Short.IIIa.RawCoeffEarly) (hRL : UnforcedLeray.Short.IIIa.RawCoeffLate)
    (hRT : UnforcedLeray.Short.IIIa.RawTransverseTail) (mZ : ℝ) (hmZ : 3 / 2 < mZ)
    (dm dp : ℝ) (hdm : 0 < dm) (a b D : ℝ) (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) :
    ∃ (Cp C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
        (∀ pt ∈ Delta.ageBelow (p.ε ^ a), 0 < pt.1 →
          Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
            C * p.ν⁻¹ ^ k * (p.ε ^ (a / 2) + p.ε)) ∧
        (∀ pt ∈ Delta.ageAbove (p.ε ^ (-b)), 0 < pt.1 →
          Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
            C * p.ν⁻¹ ^ k * (p.ε ^ (b / 2) + p.ε)) ∧
        (∀ pt ∈ Delta.tailSet (p.ε ^ a) (p.ε ^ (-b)) (Delta.transL Cp p.c p.ν (p.ε ^ (-b))),
          0 < pt.1 →
          Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
            Real.exp (-D / p.ν)) ∧
        (∀ pt ∈ (univ : Set Chart), 0 < pt.1 →
          Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
            C * p.ν⁻¹ ^ k) := by
  obtain ⟨Cp, νT, hνT, hT⟩ := hRT dm dp hdm mZ hmZ b D hb hD
  obtain ⟨C7, k7, ν7, hν7, h7⟩ := hFT mZ hmZ
  obtain ⟨C8, k8, ν8, hν8, h8⟩ := hSC dm dp hdm mZ hmZ
  obtain ⟨C9, k9, ν9, hν9, h9⟩ := hRE dm dp hdm mZ hmZ
  obtain ⟨C10, k10, ν10, hν10, h10⟩ := hRL dm dp hdm mZ hmZ
  obtain ⟨ν₀, hν₀, hν₀le⟩ := exists_pos_le_list' [νT, ν7, ν8, ν9, ν10, 1]
    (by simp [hνT, hν7, hν8, hν9, hν10])
  obtain ⟨kk, hkk⟩ : ∃ kk : ℕ, kk = k7 + k8 + k9 + k10 := ⟨_, rfl⟩
  have hmax : ∀ C : ℝ, 0 ≤ max C 0 := fun C => le_max_right C 0
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max C7 0 + max C8 0 + max C9 0 + max C10 0 := ⟨_, rfl⟩
  have := hmax C7; have := hmax C8; have := hmax C9; have := hmax C10
  have hc7 : max C7 0 ≤ c := by rw [hc]; linarith
  have hc8 : max C8 0 ≤ c := by rw [hc]; linarith
  have hc9 : max C9 0 ≤ c := by rw [hc]; linarith
  have hc10 : max C10 0 ≤ c := by rw [hc]; linarith
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  refine ⟨Cp, 2 * c, kk, ν₀, hν₀, by linarith, ?_⟩
  intro p d hBG hpν
  have hν := p.ν_pos
  have hε0 := p.ε_pos
  have hνle : ∀ x ∈ [νT, ν7, ν8, ν9, ν10, (1 : ℝ)], p.ν ≤ x :=
    fun x hx => hpν.trans (hν₀le x hx)
  have hX : 1 ≤ p.ν⁻¹ := by
    rw [le_inv_comm₀ one_pos hν, inv_one]; exact hνle 1 (by simp)
  obtain ⟨hε1, hlog⟩ := regime_facts'' hBG
  have hsm : 0 < p.ε ^ a := Real.rpow_pos_of_pos hε0 a
  have hsm1 : p.ε ^ a < 1 := Real.rpow_lt_one hε0.le hε1 ha
  have hS1 : 1 < p.ε ^ (-b) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε0 hε1 (by linarith)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = p.ν⁻¹ ^ kk := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact one_le_pow₀ hX
  have hQ0 : 0 ≤ Q := by linarith
  have hcQ : 0 ≤ c * Q := mul_nonneg hc0 hQ0
  have hws : ∀ pt : Chart, 0 ≤ Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt :=
    fun pt => mul_nonneg (Real.sqrt_nonneg _) (transWeight_nonneg' mZ pt)
  have hraw : ∀ pt : Chart, ‖trainMer p.trainData pt‖ ≤
      ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ +
        ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ := by
    intro pt
    have h := norm_sub_le (UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt)
      (UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt)
    rwa [sub_sub_cancel] at h
  have hSCp : ∀ pt : Chart, 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
        ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ ≤
          c * Q * p.ε := fun pt hpt =>
    up' (h8 p d hBG (hνle ν8 (by simp)) pt hpt) hX (by omega) hε0.le hc8 hQ
  have hBY : ∀ pt ∈ Delta.ageBelow (p.ε ^ a), 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
        c * Q * p.ε ^ (a / 2) + c * Q * p.ε := by
    intro pt hpA hpt
    have hlt : pt.1 < p.ε ^ a := hpA
    have hE := up' ((h9 p d hBG (hνle ν9 (by simp))).1 pt hpt (by linarith)) hX (by omega)
      (Real.sqrt_nonneg _) hc9 hQ
    have hsq : Real.sqrt pt.1 ≤ p.ε ^ (a / 2) := by
      calc Real.sqrt pt.1 ≤ Real.sqrt (p.ε ^ a) := Real.sqrt_le_sqrt hlt.le
        _ = p.ε ^ (a / 2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε0.le]; congr 1; ring
    calc Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖
        ≤ Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            (‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ +
              ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖) :=
          mul_le_mul_of_nonneg_left (hraw pt) (hws pt)
      _ = Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ +
          Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ := by
          ring
      _ ≤ c * Q * Real.sqrt pt.1 + c * Q * p.ε := add_le_add hE (hSCp pt hpt)
      _ ≤ c * Q * p.ε ^ (a / 2) + c * Q * p.ε := by
          have := mul_le_mul_of_nonneg_left hsq hcQ
          linarith
  have hBO : ∀ pt ∈ Delta.ageAbove (p.ε ^ (-b)), 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
        c * Q * (p.ε ^ (b / 2) + p.ε) + c * Q * p.ε := by
    intro pt hpA hpt
    have hge : p.ε ^ (-b) ≤ pt.1 := hpA
    have hE := up' ((h10 p d hBG (hνle ν10 (by simp))).1 pt (by linarith)) hX (by omega)
      (add_nonneg (Real.rpow_nonneg hpt.le _) hε0.le) hc10 hQ
    have hpow : pt.1 ^ (-1 / 2 : ℝ) ≤ p.ε ^ (b / 2) := by
      calc pt.1 ^ (-1 / 2 : ℝ) ≤ (p.ε ^ (-b)) ^ (-1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hε0 _) hge (by norm_num)
        _ = p.ε ^ (b / 2) := by rw [← Real.rpow_mul hε0.le]; congr 1; ring
    calc Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖
        ≤ Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            (‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ +
              ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖) :=
          mul_le_mul_of_nonneg_left (hraw pt) (hws pt)
      _ = Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ +
          Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ := by
          ring
      _ ≤ c * Q * (pt.1 ^ (-1 / 2 : ℝ) + p.ε) + c * Q * p.ε := add_le_add hE (hSCp pt hpt)
      _ ≤ c * Q * (p.ε ^ (b / 2) + p.ε) + c * Q * p.ε := by
          have := mul_le_mul_of_nonneg_left hpow hcQ
          linarith
  have hBT : ∀ pt ∈ Delta.tailSet (p.ε ^ a) (p.ε ^ (-b))
      (Delta.transL Cp p.c p.ν (p.ε ^ (-b))), 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
        Real.exp (-D / p.ν) := by
    intro pt hpA hpt
    obtain ⟨_, hlt, hL⟩ := hpA
    have h := hT p d hBG (hνle νT (by simp)) pt hpt hlt hL
    have heq : ‖trainMer p.trainData pt‖ = ‖p.train.v pt.1 pt.2‖ :=
      congrArg norm (Delta.trainMer_eq p.trainData pt hpt.le)
    calc Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖
        ≤ Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            (‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ + ‖p.train.v pt.1 pt.2‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (hws pt)
          rw [heq]
          linarith [norm_nonneg (UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt)]
      _ ≤ Real.exp (-D / p.ν) := h
  have hBF : ∀ pt ∈ (univ : Set Chart), 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
        c * Q := fun pt _ hpt =>
    up1' ((h7 p.ν ⟨hν, hνle ν7 (by simp)⟩ p.c hBG.c_eq p.trainData hBG.train_buc).2 pt hpt)
      hX (by omega) hc7 hQ
  have hε2 : 0 ≤ p.ε := hε0.le
  have hQe : 2 * c * p.ν⁻¹ ^ kk = 2 * (c * Q) := by rw [hQ]; ring
  refine ⟨?_, ?_, hBT, ?_⟩
  · intro pt hpA hpt
    refine (hBY pt hpA hpt).trans ?_
    rw [hQe]
    nlinarith [mul_nonneg hcQ hε2, mul_nonneg hcQ (Real.rpow_nonneg hε2 (a / 2))]
  · intro pt hpA hpt
    refine (hBO pt hpA hpt).trans ?_
    rw [hQe]
    nlinarith [mul_nonneg hcQ hε2, mul_nonneg hcQ (Real.rpow_nonneg hε2 (b / 2))]
  · intro pt hpA hpt
    refine (hBF pt hpA hpt).trans ?_
    rw [hQe]
    nlinarith

/-! ## The norm of the difference of the body forms -/

theorem body_w_norm (hN : BodyFormNorm) (p : Params) {μ : ℝ} (hμI : μ ∈ Ioo (0 : ℝ) (1 / 4))
    (Reps R0 : Hsp p.c →L[ℝ] Hsp p.c)
    (hReps : IsBodyTransport Reps
      (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)))
    (hR0 : IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)))
    (f : Hsp p.c) : ‖(Reps - R0) f‖ ≤ 8 * ‖f‖ := by
  have hμpos : 0 < (μ : ℂ).re + 1 / 4 := by
    rw [Complex.ofReal_re]; linarith [hμI.1]
  have h4 : (μ + 1 / 4)⁻¹ ≤ 4 := by
    calc (μ + 1 / 4)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith [hμI.1])
      _ = 4 := by norm_num
  have hRn := norm_RepsVec_le p.ν_pos p.ε_pos p.c_pos (P := p.period) rfl hμpos
  rw [Complex.ofReal_re] at hRn
  have hPe : ‖UnforcedLeray.Short.PartIIa.PepsC p.ε p.c‖ ≤ 1 := by
    unfold UnforcedLeray.Short.PartIIa.PepsC
    exact Submodule.starProjection_norm_le _
  have hT4 : ‖UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl
      (μ : ℂ)‖ ≤ 4 := by
    unfold UnforcedLeray.Short.PartIIa.Teps
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have := mul_le_mul (hRn.trans h4) hPe (norm_nonneg _) (by norm_num)
    linarith
  have hRf : ‖Reps f‖ ≤ 4 * ‖f‖ :=
    le_trans (hN p.c p.c_pos Reps _ hReps f) (mul_le_mul_of_nonneg_right hT4 (norm_nonneg _))
  have hR := UnforcedLeray.B0225.norm_R0_le (E := UnforcedLeray.B0223.MeridC) p.c_pos p.ν
    (μ := (μ : ℂ)) hμpos
  rw [Complex.ofReal_re] at hR
  have hRn0 : ‖(UnforcedLeray.B0225.R0 (E := UnforcedLeray.B0223.MeridC) p.c_pos p.ν (μ : ℂ))‖ ≤ 4 :=
    le_trans hR h4
  have hPe0 : ‖UnforcedLeray.Short.PartIIa.PepsC 0 p.c‖ ≤ 1 := by
    unfold UnforcedLeray.Short.PartIIa.PepsC
    exact Submodule.starProjection_norm_le _
  have hT0 : ‖UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)‖ ≤ 4 := by
    unfold UnforcedLeray.Short.PartIIa.T0flat
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have := mul_le_mul hRn0 hPe0 (norm_nonneg _) (by norm_num)
    linarith
  have hR0f : ‖R0 f‖ ≤ 4 * ‖f‖ :=
    le_trans (hN p.c p.c_pos R0 (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)) hR0 f)
      (mul_le_mul_of_nonneg_right hT0 (norm_nonneg _))
  rw [sub_apply]
  calc ‖Reps f - R0 f‖ ≤ ‖Reps f‖ + ‖R0 f‖ := norm_sub_le _ _
    _ ≤ 8 * ‖f‖ := by linarith

/-! ## The theorem -/

theorem bodyGeomColumn_of (hM1 : Delta.TrainMultRestr) (hFT : FlatTrainMultBound)
    (hSC : Delta.RawStreamCompletion) (hRE : UnforcedLeray.Short.IIIa.RawCoeffEarly)
    (hRL : UnforcedLeray.Short.IIIa.RawCoeffLate) (hRT : UnforcedLeray.Short.IIIa.RawTransverseTail)
    (hG : GainInvContract) (hN : BodyFormNorm) (hW : BodyWindowComparison) : BodyGeomColumn := by
  intro Kset hK hKsub mZ hmZ dm dp hdm
  obtain ⟨K, hK'⟩ := hW Kset hK hKsub dm dp hdm
  refine ⟨K, ?_⟩
  intro a b D ha hb hb1 hD
  obtain ⟨Cp, Ct, kt, νt, hνt, hCt, hTB⟩ := train_bounds hFT hSC hRE hRL hRT mZ hmZ dm dp hdm
    a b D ha hb hD
  obtain ⟨C1, k1, ν1, hν1, h1⟩ := hK' a b Cp ha hb hb1
  refine ⟨32 * Ct + 16 + 2 * Ct * |C1|, kt + k1, min (min νt ν1) 1, lt_min (lt_min hνt hν1) one_pos,
    ?_⟩
  intro p d hBG hpν ρb γ hρb hγ μ hμ M0 hM0 Reps R0 hReps hR0 f
  have hν := p.ν_pos
  have hε0 := p.ε_pos
  have hνt' : p.ν ≤ νt := hpν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν1' : p.ν ≤ ν1 := hpν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3 : p.ν ≤ 1 := hpν.trans (min_le_right _ _)
  have hX : 1 ≤ p.ν⁻¹ := by rw [le_inv_comm₀ one_pos hν, inv_one]; exact hν3
  obtain ⟨hε1, _⟩ := regime_facts'' hBG
  have hsm : 0 < p.ε ^ a := Real.rpow_pos_of_pos hε0 a
  have hsm1 : p.ε ^ a < 1 := Real.rpow_lt_one hε0.le hε1 ha
  have hS1 : 1 < p.ε ^ (-b) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε0 hε1 (by linarith)
  obtain ⟨hBb, hBa, hBt, hBf⟩ := hTB p d hBG hνt'
  have hY0 : 1 ≤ p.ν⁻¹ ^ kt := one_le_pow₀ hX
  have hZ0 : 1 ≤ p.ν⁻¹ ^ k1 := one_le_pow₀ hX
  have hCY : 0 ≤ Ct * p.ν⁻¹ ^ kt := mul_nonneg hCt (by linarith)
  have hwn := body_w_norm hN p (hKsub hμ) Reps R0 hReps hR0 f
  have hbox := h1 p d hBG hν1' μ hμ Reps R0 hReps hR0 f
  have hfn := norm_nonneg f
  have hsp := geom_split hG hM1 hν p.c_pos hγ p.trainData M0 hM0 (p.ε ^ a) (p.ε ^ (-b))
    (Delta.transL Cp p.c p.ν (p.ε ^ (-b))) (hsm1.trans hS1).le
    (Ct * p.ν⁻¹ ^ kt * (p.ε ^ (a / 2) + p.ε)) (Ct * p.ν⁻¹ ^ kt * (p.ε ^ (b / 2) + p.ε))
    (Real.exp (-D / p.ν)) (Ct * p.ν⁻¹ ^ kt)
    (mul_nonneg hCY (by positivity)) (mul_nonneg hCY (by positivity)) (Real.exp_pos _).le hCY
    hBb hBa hBt hBf ((Reps - R0) f)
  set A := p.ε ^ (a / 2) with hA
  set B := p.ε ^ (b / 2) with hB
  set E := p.ε with hE
  set Ex := Real.exp (-D / p.ν) with hEx
  set F := p.ε ^ (1 / 14 - (K : ℝ) * (a + b)) with hF
  set Y := p.ν⁻¹ ^ kt with hY
  set Z := p.ν⁻¹ ^ k1 with hZ
  have hpk : p.ν⁻¹ ^ (kt + k1) = Y * Z := pow_add _ _ _
  have hA0 : 0 ≤ A := Real.rpow_nonneg hε0.le _
  have hB0 : 0 ≤ B := Real.rpow_nonneg hε0.le _
  have hF0 : 0 ≤ F := Real.rpow_nonneg hε0.le _
  have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
  have hT0 : 0 ≤ A + B + E + Ex + F := by linarith
  set w := ‖(Reps - R0) f‖ with hw
  set bx := ‖Delta.outRestr p.c (Delta.binSet (p.ε ^ a) (p.ε ^ (-b))
    (Delta.transL Cp p.c p.ν (p.ε ^ (-b)))) ((Reps - R0) f)‖ with hbx
  have hw0 : 0 ≤ w := norm_nonneg _
  have hbx0 : 0 ≤ bx := norm_nonneg _
  have hbox' : bx ≤ |C1| * Z * F * ‖f‖ := by
    refine hbox.trans ?_
    have : C1 * Z ≤ |C1| * Z := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hF0) hfn
  clear_value A B E Ex F Y Z w bx
  -- the pieces
  have s1 : 2 * (Ct * Y * (A + E)) * w ≤ 16 * (Ct * Y) * (A + E) * ‖f‖ := by
    calc 2 * (Ct * Y * (A + E)) * w ≤ 2 * (Ct * Y * (A + E)) * (8 * ‖f‖) :=
          mul_le_mul_of_nonneg_left hwn (mul_nonneg (by norm_num) (mul_nonneg hCY (add_nonneg hA0 hε0.le)))
      _ = 16 * (Ct * Y) * (A + E) * ‖f‖ := by ring
  have s2 : 2 * (Ct * Y * (B + E)) * w ≤ 16 * (Ct * Y) * (B + E) * ‖f‖ := by
    calc 2 * (Ct * Y * (B + E)) * w ≤ 2 * (Ct * Y * (B + E)) * (8 * ‖f‖) :=
          mul_le_mul_of_nonneg_left hwn (mul_nonneg (by norm_num) (mul_nonneg hCY (add_nonneg hB0 hε0.le)))
      _ = 16 * (Ct * Y) * (B + E) * ‖f‖ := by ring
  have s3 : 2 * Ex * w ≤ 16 * Ex * ‖f‖ := by
    calc 2 * Ex * w ≤ 2 * Ex * (8 * ‖f‖) :=
          mul_le_mul_of_nonneg_left hwn (mul_nonneg (by norm_num) hEx0)
      _ = 16 * Ex * ‖f‖ := by ring
  have s4 : 2 * (Ct * Y) * bx ≤ 2 * (Ct * Y) * (|C1| * Z * F * ‖f‖) :=
    mul_le_mul_of_nonneg_left hbox' (mul_nonneg (by norm_num) hCY)
  have hsum : 2 * (Ct * Y * (A + E)) * w + 2 * (Ct * Y * (B + E)) * w + 2 * Ex * w +
      2 * (Ct * Y) * bx ≤ 16 * (Ct * Y) * (A + E) * ‖f‖ + 16 * (Ct * Y) * (B + E) * ‖f‖ +
        16 * Ex * ‖f‖ + 2 * (Ct * Y) * (|C1| * Z * F * ‖f‖) := by linarith only [s1, s2, s3, s4]
  refine hsp.trans (hsum.trans ?_)
  rw [hpk]
  set T := A + B + E + Ex + F with hTdef
  clear_value T
  have hYZ : 1 ≤ Y * Z := one_le_mul_of_one_le_of_one_le hY0 hZ0
  have hCYT : 0 ≤ (Ct * Y) * T := mul_nonneg hCY hT0
  have hC1 : 0 ≤ |C1| := abs_nonneg _
  have b1 : 16 * (Ct * Y) * (A + E) * ‖f‖ + 16 * (Ct * Y) * (B + E) * ‖f‖ ≤
      32 * Ct * (Y * Z) * T * ‖f‖ := by
    have e1 : 16 * (Ct * Y) * (A + E) * ‖f‖ + 16 * (Ct * Y) * (B + E) * ‖f‖ =
        16 * (Ct * Y) * (A + B + 2 * E) * ‖f‖ := by ring
    rw [e1]
    have e2 : A + B + 2 * E ≤ 2 * T := by subst hTdef; linarith only [hA0, hB0, hF0, hEx0, hε0]
    have e3 : 16 * (Ct * Y) * (A + B + 2 * E) ≤ 16 * (Ct * Y) * (2 * T) :=
      mul_le_mul_of_nonneg_left e2 (mul_nonneg (by norm_num) hCY)
    have h5 : (Ct * Y) * T ≤ (Ct * Y) * T * Z := le_mul_of_one_le_right hCYT hZ0
    have e4 : 16 * (Ct * Y) * (2 * T) ≤ 32 * Ct * (Y * Z) * T := by
      have : 32 * Ct * (Y * Z) * T = 32 * ((Ct * Y) * T * Z) := by ring
      rw [this]
      have : 16 * (Ct * Y) * (2 * T) = 32 * ((Ct * Y) * T) := by ring
      rw [this]
      linarith only [h5]
    exact mul_le_mul_of_nonneg_right (e3.trans e4) hfn
  have b2 : 16 * Ex * ‖f‖ ≤ 16 * (Y * Z) * T * ‖f‖ := by
    refine mul_le_mul_of_nonneg_right ?_ hfn
    have h7 : Ex ≤ T := by subst hTdef; linarith only [hA0, hB0, hF0, hε0]
    have h8 : T ≤ (Y * Z) * T := le_mul_of_one_le_left hT0 hYZ
    linarith only [h7, h8]
  have b3 : 2 * (Ct * Y) * (|C1| * Z * F * ‖f‖) ≤
      2 * Ct * |C1| * (Y * Z) * T * ‖f‖ := by
    have hFT' : F ≤ T := by subst hTdef; linarith only [hA0, hB0, hEx0, hε0]
    have h6 : 0 ≤ 2 * Ct * |C1| * (Y * Z) * ‖f‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCt) hC1) (by linarith)) hfn
    have := mul_le_mul_of_nonneg_left hFT' h6
    calc 2 * (Ct * Y) * (|C1| * Z * F * ‖f‖) = 2 * Ct * |C1| * (Y * Z) * ‖f‖ * F := by ring
      _ ≤ 2 * Ct * |C1| * (Y * Z) * ‖f‖ * T := this
      _ = 2 * Ct * |C1| * (Y * Z) * T * ‖f‖ := by ring
  have : (32 * Ct + 16 + 2 * Ct * |C1|) * (Y * Z) * T * ‖f‖ =
      32 * Ct * (Y * Z) * T * ‖f‖ + 16 * (Y * Z) * T * ‖f‖ +
        2 * Ct * |C1| * (Y * Z) * T * ‖f‖ := by ring
  rw [this]
  linarith only [b1, b2, b3]

end UnforcedLeray.Short.PartIIIb.NearInst.Body
