import UnforcedLeray.Lib.LerayLp.Cutoff

/-!
# Helmholtz facts for the `L^p` Leray projection (INF01 T15)


§5, Level 2, in the restricted form of §4.8 (`lerayLp_isSolenoidal`, `lerayLp_eq_self`,
`lerayLp_gradient_eq_zero`, `lerayLp_idem`); decision D5 of `scoping/README.md` §3.

Manuscript:
* unit B0797 (eq:ward:W2.6, `paper/main.tex` lines 11539–11560): "`L_{free,0}U_raw` is in
  `L^{p_0}` … distributionally solenoidal, so its Helmholtz complement vanishes", and
  "`(I − P)∇p_lift = ∇p_lift`";
* unit B0439 (lines 7364–7387): "surjectivity uses `g = P_σ g` on `Y_{q,σ}`";
* unit B0414 (lines 7336–7344): `P_σ` is a projection onto the solenoidal fields.

Statements, for `1 < p < ∞`:
* `lerayLp_isSolenoidal`: `𝔓F` is distributionally solenoidal (`IsSolenoidal` of
  `Statement.lean`, including the integrability of its test pairings);
* `lerayLp_eq_self` (**T15**, "`𝔓 = id` on solenoidal `L^p`"): if `F ∈ L^p` is distributionally
  solenoidal then `𝔓F = F`;
* `lerayLp_idem`: `𝔓 ∘ 𝔓 = 𝔓`;
* `lerayLp_gradient_eq_zero`: if `φ` is smooth, `φ ∈ L^r` for some `1 ≤ r ≤ ∞`, and
  `∇φ ∈ L^p`, then `𝔓∇φ = 0`. This is the decaying case of §4.8; the general statement
  "`∇φ ∈ L^p ⇒ 𝔓∇φ = 0`" (a Liouville argument) is not proved here.

Proofs (§4.8 of the note): duality `∫ ⟨𝔓F, G⟩ = ∫ ⟨F, 𝔓G⟩` for vector tests `G`
(`Duality.lean`), the test-level formula `𝔓G = G + ∇ψ`, `ψ = N ∗ div G`
(`Lib/CZL2/TestProjection.lean`), and the cutoff lemma `integral_inner_gradField_eq_zero`
(`Cutoff.lean`) with the decay `|ψ| ≲ (1 + |x|)⁻²`, `|∇ψ| ≲ (1 + |x|)⁻³`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.RieszLp

/-! ### Exponent bookkeeping -/

/-- The conjugate exponent `p' ≥ 1`. -/
theorem one_le_conjExponent (p : ℝ≥0∞) [Fact (1 ≤ p)] : 1 ≤ p.conjExponent :=
  ENNReal.HolderConjugate.one_le _ p

theorem one_lt_toReal_of_one_lt {q : ℝ≥0∞} (hq1 : 1 < q) (hq : q ≠ ⊤) : 1 < q.toReal := by
  have := ENNReal.toReal_strict_mono hq hq1
  rwa [ENNReal.toReal_one] at this

/-- `(1 + |x|)⁻³ ∈ L^q` for `1 < q`. -/
theorem memLp_powWeight_three {q : ℝ≥0∞} (hq1 : 1 < q) : MemLp (powWeight 3) q volume := by
  refine memLp_powWeight (by norm_num) (lt_trans zero_lt_one hq1).ne' ?_
  by_cases hq : q = ⊤
  · exact Or.inl hq
  · right
    have := one_lt_toReal_of_one_lt hq1 hq
    linarith

/-- `(1 + |x|)⁻⁴ ∈ L^q` for `1 ≤ q`. -/
theorem memLp_powWeight_four {q : ℝ≥0∞} (hq1 : 1 ≤ q) : MemLp (powWeight 4) q volume := by
  refine memLp_powWeight (by norm_num) (lt_of_lt_of_le zero_lt_one hq1).ne' ?_
  by_cases hq : q = ⊤
  · exact Or.inl hq
  · right
    have h1 : (1 : ℝ) ≤ q.toReal := by
      have := ENNReal.toReal_mono hq hq1
      rwa [ENNReal.toReal_one] at this
    linarith

/-! ### Pairing identities -/

theorem inner_smul_coordinateVector (v : Space) (c : ℝ) (j : Fin 3) :
    inner ℝ v (c • coordinateVector j) = c * v j := by
  rw [real_inner_smul_right, coordinateVector, EuclideanSpace.inner_single_right]
  simp

/-- The `L²` class of a test gradient is `Leray.testGradient`. -/
theorem toL2_gradField_test {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    toL2 (gradField φ) = Leray.testGradient φ hφ := by
  have hg : MemLp (gradField φ) 2 volume := by
    rw [gradField_eq_vecField]
    exact memLp_vecField (fun i => hφ.derivative i) 2
  apply Lp.ext
  filter_upwards [coeFn_toL2 hg, Leray.coeFn_testGradient φ hφ] with x h1 h2
  rw [h1, h2]
  rfl

theorem memLp_gradField_test {φ : Space → ℝ} (hφ : IsSpatialTest φ) (s : ℝ≥0∞) :
    MemLp (gradField φ) s volume := by
  rw [gradField_eq_vecField]
  exact memLp_vecField (fun i => hφ.derivative i) s

/-- The orthogonal Leray projection kills test gradients. -/
theorem projection_toL2_gradField_test {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    Leray.projection (toL2 (gradField φ)) = 0 := by
  rw [toL2_gradField_test hφ, Leray.projection]
  exact (Submodule.starProjection_apply_eq_zero_iff _).2 (Leray.testGradient_mem_orthogonal φ hφ)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Duality with an `L² ∩ L^{p'}` field.** For `F ∈ L^p` and `G ∈ L² ∩ L^{p'}`,
`∫ ⟨𝔓F, G⟩ = ∫ ⟨F, P G⟩` with `P` the orthogonal Leray projection. -/
theorem integral_inner_lerayLp_eq_projection (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : Lp Space p (volume : Measure Space)) {G : SpatialField}
    (hGq : MemLp G p.conjExponent volume) (hG2 : MemLp G 2 volume) :
    ∫ x, inner ℝ (lerayLp p hp1 hp F x) (G x) =
      ∫ x, inner ℝ (F x) (Leray.projection (toL2 G) x) := by
  have : Fact (1 ≤ p.conjExponent) := ⟨one_le_conjExponent p⟩
  have hq1 : 1 < p.conjExponent := one_lt_of_holderConjugate hp
  have hq : p.conjExponent ≠ ⊤ := ne_top_of_holderConjugate hp1
  have e1 : ∫ x, inner ℝ (lerayLp p hp1 hp F x) (G x) =
      ∫ x, inner ℝ (lerayLp p hp1 hp F x) ((hGq.toLp G) x) := by
    refine integral_congr_ae ?_
    filter_upwards [hGq.coeFn_toLp] with x hx
    rw [hx]
  rw [e1, integral_inner_lerayLp_of_memLp_two hp1 hp hq1 hq F (hGq.toLp G)
    (hG2.ae_eq hGq.coeFn_toLp.symm)]
  refine integral_congr_ae ?_
  filter_upwards [lerayLp_toLp_ae_eq_projection hq1 hq hGq hG2] with x hx
  rw [hx]

/-- For a vector test `f`, `∫ ⟨𝔓F, f⟩ = ∫ ⟨F, f + ∇(N ∗ div f)⟩`. -/
theorem integral_inner_lerayLp_vecField (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : Lp Space p (volume : Measure Space)) {f : Fin 3 → Space → ℝ}
    (hf : ∀ j, IsSpatialTest (f j)) :
    ∫ x, inner ℝ (lerayLp p hp1 hp F x) (vecField f x) =
      ∫ x, inner ℝ (F x) (vecField f x + gradField (lerayPotential f) x) := by
  rw [integral_inner_lerayLp_eq_projection hp1 hp F (memLp_vecField hf _)
    (memLp_vecField hf 2), projection_toL2_vecField hf]
  have hW : MemLp (vecField f + gradField (lerayPotential f)) 2 volume :=
    (memLp_vecField hf 2).add (memLp_gradField_lerayPotential hf)
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 hW] with x hx
  rw [hx]
  rfl

/-! ### T15 -/

/-- **INF01 T15.** `𝔓F` is distributionally solenoidal for every `F ∈ L^p(R³;R³)`. -/
theorem lerayLp_isSolenoidal (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : Lp Space p (volume : Measure Space)) :
    IsSolenoidal (lerayLp p hp1 hp F : SpatialField) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · exact (integrable_inner_of_memLp (Lp.memLp (lerayLp p hp1 hp F))
      (memLp_gradField_test hφ p.conjExponent)).congr
      (Eventually.of_forall fun x => inner_gradField _ φ x)
  · rw [← integral_congr_ae (Eventually.of_forall fun x =>
      inner_gradField (lerayLp p hp1 hp F x) φ x)]
    rw [integral_inner_lerayLp_eq_projection hp1 hp F (memLp_gradField_test hφ _)
      (memLp_gradField_test hφ 2), projection_toL2_gradField_test hφ]
    have h0 : (fun x => inner ℝ (F x) (((0 : L2Space) : SpatialField) x)) =ᵐ[volume]
        fun _ => (0 : ℝ) := by
      filter_upwards [Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx
      rw [hx, Pi.zero_apply, inner_zero_right]
    rw [integral_congr_ae h0, integral_zero]

/-- Bounds for the potential of a vector test: `|ψ| (1 + |x|)⁻¹ ≲ (1 + |x|)⁻³`,
`|∇ψ| ≲ (1 + |x|)⁻³`, and `∇ψ ∈ L^q` for `q > 1`. -/
theorem lerayPotential_bounds {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j)) :
    ∃ M, 0 ≤ M ∧ (∀ x, |lerayPotential f x| * (1 + ‖x‖)⁻¹ ≤ M * powWeight 3 x) ∧
      ∀ x, ‖gradField (lerayPotential f) x‖ ≤ M * powWeight 3 x := by
  obtain ⟨A, hA, -⟩ := lerayPotential_decay hf
  obtain ⟨B, hB⟩ := lerayPotential_grad_decay hf
  refine ⟨|A| + 3 * |B|, by positivity, fun x => ?_, fun x => ?_⟩
  · have hw := powWeight_pos 3 x
    have e : decayWeight x * (1 + ‖x‖)⁻¹ = powWeight 3 x := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, powWeight_natCast, decayWeight, ← mul_inv]
      ring
    calc |lerayPotential f x| * (1 + ‖x‖)⁻¹ ≤ A * decayWeight x * (1 + ‖x‖)⁻¹ :=
          mul_le_mul_of_nonneg_right (hA x) (by positivity)
      _ = A * powWeight 3 x := by rw [mul_assoc, e]
      _ ≤ (|A| + 3 * |B|) * powWeight 3 x := by
          gcongr
          linarith [le_abs_self A, abs_nonneg B]
  · have hw := powWeight_pos 3 x
    refine (norm_sum_smul_coordinateVector_le _).trans ?_
    calc ∑ i : Fin 3, |spatialTestDerivative i (lerayPotential f) x|
        ≤ ∑ _i : Fin 3, |B| * powWeight 3 x :=
          Finset.sum_le_sum fun i _ => (hB i x).trans
            (mul_le_mul_of_nonneg_right (le_abs_self B) hw.le)
      _ = 3 * |B| * powWeight 3 x := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ (|A| + 3 * |B|) * powWeight 3 x := by
          gcongr
          linarith [abs_nonneg A]

/-- `∇(N ∗ div f) ∈ L^q` for `q > 1`. -/
theorem memLp_gradField_lerayPotential' {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j))
    {q : ℝ≥0∞} (hq1 : 1 < q) : MemLp (gradField (lerayPotential f)) q volume := by
  obtain ⟨M, -, -, hM⟩ := lerayPotential_bounds hf
  refine ((memLp_powWeight_three hq1).const_mul M).of_le
    (continuous_gradField (lerayPotential_contDiff hf)).aestronglyMeasurable
    (Eventually.of_forall fun x => (hM x).trans ?_)
  rw [Real.norm_eq_abs]
  exact le_abs_self _

/-- **INF01 T15 ("`𝔓 = id` on solenoidal `L^p`").** If `F ∈ L^p(R³;R³)`, `1 < p < ∞`, is
distributionally solenoidal, then `𝔓F = F` (unit B0797, `paper/main.tex` lines 11539–11560;
unit B0439, lines 7364–7387). -/
theorem lerayLp_eq_self (hp1 : 1 < p) (hp : p ≠ ⊤) (F : Lp Space p (volume : Measure Space))
    (h : IsSolenoidal (F : SpatialField)) : lerayLp p hp1 hp F = F := by
  have hq1 : 1 < p.conjExponent := one_lt_of_holderConjugate hp
  have hH : ∀ j : Fin 3, ∀ᵐ x ∂volume, (lerayLp p hp1 hp F x - F x) j = 0 := by
    intro j
    have hloc : LocallyIntegrable (fun x => (lerayLp p hp1 hp F x - F x) j) volume :=
      (memLp_component p ((Lp.memLp (lerayLp p hp1 hp F)).sub (Lp.memLp F)) j).locallyIntegrable
        Fact.out
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hgs hgc => ?_
    have hg : IsSpatialTest g := ⟨hgs, hgc⟩
    have hfam := isSpatialTest_singleFamily hg j
    set fam := singleFamily j g with hfamdef
    set ψ := lerayPotential fam with hψdef
    have hVq := memLp_vecField hfam p.conjExponent
    have hWq := memLp_gradField_lerayPotential' hfam hq1
    have e1 : ∀ x, g x • (lerayLp p hp1 hp F x - F x) j =
        inner ℝ (lerayLp p hp1 hp F x) (vecField fam x) - inner ℝ (F x) (vecField fam x) := by
      intro x
      rw [vecField_singleFamily, ← inner_sub_left, inner_smul_coordinateVector, smul_eq_mul]
    have hA : Integrable (fun x => inner ℝ (F x) (vecField fam x + gradField ψ x)) volume :=
      integrable_inner_of_memLp (Lp.memLp F) (hVq.add hWq)
    have hB : Integrable (fun x => inner ℝ (F x) (vecField fam x)) volume :=
      integrable_inner_of_memLp (Lp.memLp F) hVq
    rw [integral_congr_ae (Eventually.of_forall e1),
      integral_sub (integrable_inner_of_memLp (Lp.memLp _) hVq) hB,
      integral_inner_lerayLp_vecField hp1 hp F hfam, ← integral_sub hA hB]
    have e2 : ∀ x, inner ℝ (F x) (vecField fam x + gradField ψ x) -
        inner ℝ (F x) (vecField fam x) = inner ℝ (F x) (gradField ψ x) := by
      intro x
      rw [inner_add_right]
      ring
    simp_rw [e2]
    obtain ⟨M, hM0, hMψ, hMg⟩ := lerayPotential_bounds hfam
    have hFw := integrable_norm_mul_of_memLp (Lp.memLp F) (memLp_powWeight_three hq1)
    refine integral_inner_gradField_eq_zero h (Lp.aestronglyMeasurable F)
      (lerayPotential_contDiff hfam) ?_ ?_
    · refine (hFw.const_mul M).mono'
        ((Lp.aestronglyMeasurable F).norm.mul
          (continuous_gradField (lerayPotential_contDiff hfam)).aestronglyMeasurable.norm)
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖F x‖ * ‖gradField ψ x‖ ≤ ‖F x‖ * (M * powWeight 3 x) :=
            mul_le_mul_of_nonneg_left (hMg x) (norm_nonneg _)
        _ = M * (‖F x‖ * powWeight 3 x) := by ring
    · refine (hFw.const_mul M).mono'
        (((Lp.aestronglyMeasurable F).norm.mul
          (lerayPotential_contDiff hfam).continuous.aestronglyMeasurable.norm).mul
          ((continuous_const.add continuous_norm).inv₀ fun x =>
            (by positivity : (0 : ℝ) < 1 + ‖x‖).ne').aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖F x‖ * |ψ x| * (1 + ‖x‖)⁻¹ = ‖F x‖ * (|ψ x| * (1 + ‖x‖)⁻¹) := by ring
        _ ≤ ‖F x‖ * (M * powWeight 3 x) := mul_le_mul_of_nonneg_left (hMψ x) (norm_nonneg _)
        _ = M * (‖F x‖ * powWeight 3 x) := by ring
  apply Lp.ext
  filter_upwards [ae_all_iff.2 hH] with x hx
  ext j
  have := hx j
  rw [PiLp.sub_apply] at this
  linarith

/-- **INF01 T15.** `𝔓` is idempotent on `L^p(R³;R³)`. -/
theorem lerayLp_idem (hp1 : 1 < p) (hp : p ≠ ⊤) :
    (lerayLp p hp1 hp).comp (lerayLp p hp1 hp) = lerayLp p hp1 hp := by
  ext1 F
  rw [ContinuousLinearMap.comp_apply]
  exact lerayLp_eq_self hp1 hp _ (lerayLp_isSolenoidal hp1 hp F)

/-- **INF01 T15 (decaying gradients, §4.8).** If `φ` is smooth, `φ ∈ L^r` for some `r ≥ 1`
(`r = ∞` allowed) and `∇φ ∈ L^p`, `1 < p < ∞`, then `𝔓∇φ = 0` (unit B0797,
`paper/main.tex` lines 11539–11560: "`(I − P)∇p_lift = ∇p_lift`"). -/
theorem lerayLp_gradient_eq_zero (hp1 : 1 < p) (hp : p ≠ ⊤) {φ : Space → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {r : ℝ≥0∞} (hr : 1 ≤ r) (hφr : MemLp φ r volume)
    (hg : MemLp (gradField φ) p volume) :
    lerayLp p hp1 hp (hg.toLp (gradField φ)) = 0 := by
  have : Fact (1 ≤ r) := ⟨hr⟩
  have hq1 : 1 < p.conjExponent := one_lt_of_holderConjugate hp
  set P := lerayLp p hp1 hp (hg.toLp (gradField φ)) with hPdef
  have hH : ∀ j : Fin 3, ∀ᵐ x ∂volume, (P x) j = 0 := by
    intro j
    have hloc : LocallyIntegrable (fun x => (P x) j) volume :=
      (memLp_component p (Lp.memLp P) j).locallyIntegrable Fact.out
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hgs hgc => ?_
    have hgt : IsSpatialTest g := ⟨hgs, hgc⟩
    have hfam := isSpatialTest_singleFamily hgt j
    set fam := singleFamily j g with hfamdef
    set ψ := lerayPotential fam with hψdef
    set V : SpatialField := vecField fam + gradField ψ with hVdef
    have hVsol : IsSolenoidal V := isSolenoidal_vecField_add_gradField hfam
    have hVq : MemLp V p.conjExponent volume :=
      (memLp_vecField hfam _).add (memLp_gradField_lerayPotential' hfam hq1)
    have hVc : Continuous V :=
      (continuous_vecField fun i => (hfam i).continuous).add
        (continuous_gradField (lerayPotential_contDiff hfam))
    have e1 : ∀ x, g x • (P x) j = inner ℝ (P x) (vecField fam x) := by
      intro x
      rw [vecField_singleFamily, inner_smul_coordinateVector, smul_eq_mul]
    rw [integral_congr_ae (Eventually.of_forall e1), integral_inner_lerayLp_vecField hp1 hp _ hfam]
    have e2 : (fun x => inner ℝ ((hg.toLp (gradField φ) : SpatialField) x)
        (vecField fam x + gradField ψ x)) =ᵐ[volume] fun x => inner ℝ (V x) (gradField φ x) := by
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx, real_inner_comm]
      rfl
    rw [integral_congr_ae e2]
    -- pointwise bound `|V| ≲ (1 + |x|)⁻³`
    obtain ⟨M, hM0, -, hMg⟩ := lerayPotential_bounds hfam
    obtain ⟨M1, hM1⟩ := test_decay hgt
    have hVb : ∀ x, ‖V x‖ ≤ (3 * |M1| + M) * powWeight 3 x := by
      intro x
      have hw := powWeight_pos 3 x
      have hv : ‖vecField fam x‖ ≤ 3 * |M1| * powWeight 3 x := by
        refine (norm_sum_smul_coordinateVector_le _).trans ?_
        calc ∑ i : Fin 3, |fam i x| ≤ ∑ _i : Fin 3, |M1| * powWeight 3 x := by
              refine Finset.sum_le_sum fun i _ => ?_
              have h0 : |fam i x| ≤ |g x| := by
                rw [hfamdef, singleFamily]
                split_ifs
                · exact le_rfl
                · rw [abs_zero]; exact abs_nonneg _
              exact h0.trans ((hM1 x).trans (mul_le_mul_of_nonneg_right (le_abs_self M1) hw.le))
          _ = 3 * |M1| * powWeight 3 x := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
      calc ‖V x‖ ≤ ‖vecField fam x‖ + ‖gradField ψ x‖ := norm_add_le _ _
        _ ≤ 3 * |M1| * powWeight 3 x + M * powWeight 3 x := add_le_add hv (hMg x)
        _ = (3 * |M1| + M) * powWeight 3 x := by ring
    have hK0 : 0 ≤ 3 * |M1| + M := by positivity
    refine integral_inner_gradField_eq_zero hVsol hVc.aestronglyMeasurable hφ ?_ ?_
    · exact integrable_norm_mul_of_memLp hVq hg.norm
    · have hr' : 1 ≤ r.conjExponent := one_le_conjExponent r
      have hφw := integrable_norm_mul_of_memLp hφr (memLp_powWeight_four hr')
      refine (hφw.const_mul (3 * |M1| + M)).mono'
        (((hVc.aestronglyMeasurable.norm).mul hφ.continuous.aestronglyMeasurable.norm).mul
          ((continuous_const.add continuous_norm).inv₀ fun x =>
            (by positivity : (0 : ℝ) < 1 + ‖x‖).ne').aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      have hpos : 0 < 1 + ‖x‖ := by positivity
      rw [Real.norm_of_nonneg (by positivity)]
      have e4 : powWeight 3 x * (1 + ‖x‖)⁻¹ = powWeight 4 x := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
          powWeight_natCast, powWeight_natCast, ← mul_inv]
        ring
      calc ‖V x‖ * |φ x| * (1 + ‖x‖)⁻¹
          ≤ (3 * |M1| + M) * powWeight 3 x * |φ x| * (1 + ‖x‖)⁻¹ := by
            gcongr
            exact hVb x
        _ = (3 * |M1| + M) * (‖φ x‖ * (powWeight 3 x * (1 + ‖x‖)⁻¹)) := by
            rw [Real.norm_eq_abs]
            ring
        _ = (3 * |M1| + M) * (‖φ x‖ * powWeight 4 x) := by rw [e4]
  apply Lp.ext
  filter_upwards [ae_all_iff.2 hH, Lp.coeFn_zero Space p (volume : Measure Space)] with x hx h0
  rw [h0]
  ext j
  rw [hx j]
  rfl

end UnforcedLeray.RieszLp
