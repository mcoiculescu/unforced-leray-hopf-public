import UnforcedLeray.Units.B0121.Forward

/-!
# B0121 helper: Gaussian-`L²` weak derivatives up to order `j` force `f ∈ X_{G,j}`

Blueprint unit B0121 (`eq:st18-t00100`, `paper/main.tex` lines 1856--1865), the direction
"derivatives control the graph norm". Let the planar function of `f ∈ X_G` have weak
derivatives `g α = ∂^α f ∈ L²(ℝ², G⁻¹ dy)` for all `|α| ≤ j` (`IsWeakFamily`). Then for every
word `w` the derivative `g (mi w)` is the weak `∂_w` derivative (`IsWeakFamily.word`), and
derivatives can be moved onto test functions `U_G⁻¹`-conjugate to finite combinations of
Hermite levels (`IsWeakFamily.peel`, polynomial test functions). Duality with the level
identity `∑_{|w|=k} B_w A_w = Q_k` bounds `2π ∑_{ℓ<M} qsum j ℓ |⟪e_ℓ, f⟫|²` by the sum of the
squared Gaussian norms of the derivatives (`two_pi_sum_le`), uniformly in `M`; hence
`f ∈ X_{G,j}` (`mem_XGj_of_isWeakFamily`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap InnerProductSpace ComplexConjugate Real ENNReal ContDiff

namespace UnforcedLeray.B0121

open UnforcedLeray.B0094 UnforcedLeray.B0010 UnforcedLeray.PlanarBS.Sob

/-- `g α = ∂^α F` weakly, with `g α ∈ L²(ℝ², G⁻¹ dy)`, for every multi-index `|α| ≤ j`
(the derivatives of `eq:st18-t00100`). -/
def IsWeakFamily (j : ℕ) (F : ℝ × ℝ → ℂ) (g : ℕ × ℕ → ℝ × ℝ → ℂ) : Prop :=
  ∀ α ∈ multiIdx j, MemGaussL2 (g α) ∧ HasWeakDerivOn univ (pdListR α) F (g α)

theorem mi_mem_multiIdx {j k : ℕ} (hk : k ≤ j) (w : Fin k → Fin 2) : mi w ∈ multiIdx j := by
  have h := mi_mem_antidiagonal w
  rw [Finset.mem_antidiagonal] at h
  rw [mem_multiIdx]
  omega

/-- The derivative of the multi-index of a word is the weak derivative along the word. -/
theorem IsWeakFamily.word {j : ℕ} {F : ℝ × ℝ → ℂ} {g : ℕ × ℕ → ℝ × ℝ → ℂ}
    (h : IsWeakFamily j F g) {k : ℕ} (hk : k ≤ j) (w : Fin k → Fin 2) :
    MemGaussL2 (g (mi w)) ∧ HasWeakDerivOn univ (dirs w) F (g (mi w)) := by
  obtain ⟨h1, h2⟩ := h _ (mi_mem_multiIdx hk w)
  exact ⟨h1, hasWeakDerivOn_perm (dirs_perm w).symm h2⟩

/-- `g (mi w) = ∂_{w 0} g (mi (tail w))` weakly. -/
theorem IsWeakFamily.step {j : ℕ} {F : ℝ × ℝ → ℂ} {g : ℕ × ℕ → ℝ × ℝ → ℂ}
    (h : IsWeakFamily j F g) {k : ℕ} (hk : k + 1 ≤ j) (w : Fin (k + 1) → Fin 2)
    (φ : ℝ × ℝ → ℂ) (hφ : IsTestFn univ φ) :
    ∫ z, g (mi (Fin.tail w)) z * dirDeriv (ev (w 0)) φ z = -∫ z, g (mi w) z * φ z := by
  have h1 := (h.word (by omega : k ≤ j) (Fin.tail w)).2 (dirDeriv (ev (w 0)) φ)
    (hφ.dirDeriv _)
  have h2 := (h.word hk w).2 φ hφ
  have e : iterDirDeriv (dirs (Fin.tail w)) (dirDeriv (ev (w 0)) φ) =
      iterDirDeriv (dirs w) φ := by
    rw [dirs_succ, ← iterDirDeriv_perm (List.perm_append_singleton _ _) hφ.smooth,
      iterDirDeriv_append]
    rfl
  rw [e, h2, dirs_length, dirs_length] at h1
  have hne : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (-1 : ℂ) ^ k * ∫ z, g (mi (Fin.tail w)) z * dirDeriv (ev (w 0)) φ z =
      (-1 : ℂ) ^ k * -∫ z, g (mi w) z * φ z := by
    rw [← h1, pow_succ]
    ring
  exact mul_left_cancel₀ hne h3

theorem integrable_mul_conj_conjG {F : ℝ × ℝ → ℂ} (hF : MemGaussL2 F) {η : S2} (hη : IsGP η) :
    Integrable (fun z => F z * conj (B0093.conjG ⇑η z)) volume := by
  obtain ⟨P, hP, hηP⟩ := hη
  have h := integrable_mul_temperate hF (hasTemperateGrowth_conj hP)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only
  rw [IsGP.conjG_eq hηP]

/-- **Moving all derivatives to the test function**: for a word `w` of length `k ≤ j` and
`η = √G P`, `∫ ∂_w f · conj(U_G η) = ∫ f · conj(U_G (B_w η))`. -/
theorem IsWeakFamily.peel {j : ℕ} {F : ℝ × ℝ → ℂ} {g : ℕ × ℕ → ℝ × ℝ → ℂ}
    (h : IsWeakFamily j F g) (hF : MemGaussL2 F) {k : ℕ} (hk : k ≤ j) (w : Fin k → Fin 2)
    {η : S2} (hη : IsGP η) :
    ∫ z, g (mi w) z * conj (B0093.conjG ⇑η z) =
      ∫ z, F z * conj (B0093.conjG ⇑(Bw k w η) z) := by
  induction k generalizing η with
  | zero =>
    have hw := (h.word hk w)
    have hFF : HasWeakDerivOn univ (dirs w) F F := by
      intro φ _
      simp [dirs]
    have hae := hasWeakDerivOn_ae_eq isOpen_univ (hw.1.locallyIntegrable.locallyIntegrableOn univ)
      (hF.locallyIntegrable.locallyIntegrableOn univ) hw.2 hFF
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz (mem_univ z)]
    rfl
  | succ k ih =>
    have hw := h.word hk w
    have hw' := h.word (by omega : k ≤ j) (Fin.tail w)
    rw [integral_peel hw'.1 hw.1 (w 0) (h.step hk w) hη, ih (by omega) (Fin.tail w) (hη.Bop _),
      Bw_succ]

theorem schwartz_sum_apply {ι : Type*} (s : Finset ι) (ζ : ι → S2) (z : ℝ × ℝ) :
    (∑ i ∈ s, ζ i) z = ∑ i ∈ s, ζ i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

/-- `∑_{|w| = k} ∫ ∂_w f · conj(U_G A_w χ) = ∫ f · conj(U_G Q_k χ)`. -/
theorem IsWeakFamily.sum_peel {j : ℕ} {F : ℝ × ℝ → ℂ} {g : ℕ × ℕ → ℝ × ℝ → ℂ}
    (h : IsWeakFamily j F g) (hF : MemGaussL2 F) {k : ℕ} (hk : k ≤ j) {χ : S2} (hχ : IsGP χ) :
    ∑ w : Fin k → Fin 2, ∫ z, g (mi w) z * conj (B0093.conjG ⇑(Aw k w χ) z) =
      ∫ z, F z * conj (B0093.conjG ⇑(Qop k χ) z) := by
  simp_rw [h.peel hF hk _ (hχ.Aw k _)]
  rw [← integral_finset_sum _ fun w _ => integrable_mul_conj_conjG hF ((hχ.Aw k w).Bw w)]
  congr 1
  funext z
  rw [← sum_Bw_Aw]
  conv_rhs => rw [conjG_apply, schwartz_sum_apply, Finset.mul_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [conjG_apply]

theorem norm_integral_mul_conj_conjG_le {g : ℝ × ℝ → ℂ} (hg : MemGaussL2 g) (ζ : S2) :
    ‖∫ z, g z * conj (B0093.conjG ⇑ζ z)‖ ≤ ‖hg.toLp (B0093.conjG g)‖ * ‖J ζ‖ := by
  have hs : MemLp (star ⇑ζ) 2 volume := (ζ.memLp 2 volume).star
  have e : ∫ z, g z * conj (B0093.conjG ⇑ζ z) = ∫ z, B0093.conjG g z * (star ⇑ζ) z := by
    congr 1
    funext z
    rw [conjG_apply, conjG_apply, Pi.star_apply, map_mul, Complex.conj_ofReal]
    simp only [RCLike.star_def]
    ring
  rw [e]
  refine (norm_integral_mul_le hg hs).trans (le_of_eq ?_)
  congr 1
  exact norm_toLp_star (ζ.memLp 2 volume)

/-- The pairing of `f` with `U_G⁻¹ Q_k` of its own truncation. -/
theorem integral_planar_Qop_trunc (f : XG) (k M : ℕ) :
    ∫ z, planar f z * conj (B0093.conjG ⇑(Qop k (trunc f M)) z) =
      ((2 * π * ∑ ℓ ∈ Finset.range M, qpoly k (2 + ℓ) * ‖coef f ℓ‖ ^ 2 : ℝ) : ℂ) := by
  rw [trunc, Qop_chi, integral_planar_mul_conj_conjG f (isAngularTwo_chi _ _), toXG_chi,
    sum_inner]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [inner_smul_left, map_mul, Complex.conj_ofReal]
  change conj (coef f ℓ) * _ * coef f ℓ = _
  rw [mul_comm (conj (coef f ℓ)), mul_assoc, mul_comm (conj (coef f ℓ)), Complex.mul_conj']

/-- **The duality bound**: `2π ∑_{ℓ<M} qsum j ℓ |⟪e_ℓ, f⟫|² ≤ ∑_{k ≤ j} ∑_{|w|=k} ‖∂_w f‖²`. -/
theorem two_pi_sum_le {j : ℕ} {f : XG} {g : ℕ × ℕ → ℝ × ℝ → ℂ}
    (h : IsWeakFamily j (planar f) g) (M : ℕ) :
    2 * π * ∑ ℓ ∈ Finset.range M, qsum j ℓ * ‖coef f ℓ‖ ^ 2 ≤
      ∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2, gaussNormSq (g (mi w)) := by
  set χ := trunc f M with hχ
  have hχGP : IsGP χ := isGP_chi _ _
  have hF := memGaussL2_planar f
  set S := ∑ ℓ ∈ Finset.range M, qsum j ℓ * ‖coef f ℓ‖ ^ 2 with hS
  -- the level sums
  have hlev : ∀ k, ∑ w : Fin k → Fin 2, ‖J (Aw k w χ)‖ ^ 2 =
      2 * π * ∑ ℓ ∈ Finset.range M, qpoly k (2 + ℓ) * ‖coef f ℓ‖ ^ 2 :=
    fun k => sum_norm_sq_Aw_chi k _ _
  have hSk : ∑ k ∈ Finset.range (j + 1),
      (2 * π * ∑ ℓ ∈ Finset.range M, qpoly k (2 + ℓ) * ‖coef f ℓ‖ ^ 2) = 2 * π * S := by
    rw [← Finset.mul_sum, Finset.sum_comm, hS]
    congr 1
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [qsum, Finset.sum_mul]
  -- the pairings
  have hT : ∀ k ∈ Finset.range (j + 1),
      ∑ w : Fin k → Fin 2, ∫ z, g (mi w) z * conj (B0093.conjG ⇑(Aw k w χ) z) =
        ((2 * π * ∑ ℓ ∈ Finset.range M, qpoly k (2 + ℓ) * ‖coef f ℓ‖ ^ 2 : ℝ) : ℂ) := by
    intro k hk
    rw [h.sum_peel hF (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hχGP, hχ,
      integral_planar_Qop_trunc]
  -- each term
  have hterm : ∀ k ∈ Finset.range (j + 1), ∀ w : Fin k → Fin 2,
      (∫ z, g (mi w) z * conj (B0093.conjG ⇑(Aw k w χ) z)).re ≤
        (gaussNormSq (g (mi w)) + ‖J (Aw k w χ)‖ ^ 2) / 2 := by
    intro k hk w
    have hg := (h.word (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) w).1
    have h1 := norm_integral_mul_conj_conjG_le hg (Aw k w χ)
    have h2 := Complex.re_le_norm (∫ z, g (mi w) z * conj (B0093.conjG ⇑(Aw k w χ) z))
    have h3 := norm_toLp_sq hg
    set a := ‖hg.toLp (B0093.conjG (g (mi w)))‖
    set b := ‖J (Aw k w χ)‖
    nlinarith [sq_nonneg (a - b)]
  have key : 2 * π * S ≤
      (∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2, gaussNormSq (g (mi w)) + 2 * π * S) / 2 := by
    calc 2 * π * S
        = (∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2,
            ∫ z, g (mi w) z * conj (B0093.conjG ⇑(Aw k w χ) z)).re := by
          rw [Finset.sum_congr rfl hT, ← Complex.ofReal_sum, Complex.ofReal_re, hSk]
      _ = ∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2,
            (∫ z, g (mi w) z * conj (B0093.conjG ⇑(Aw k w χ) z)).re := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Complex.re_sum]
      _ ≤ ∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2,
            (gaussNormSq (g (mi w)) + ‖J (Aw k w χ)‖ ^ 2) / 2 :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun w _ => hterm k hk w
      _ = (∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2, gaussNormSq (g (mi w)) +
            ∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2, ‖J (Aw k w χ)‖ ^ 2) / 2 := by
          rw [add_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => ?_
          ring
      _ = (∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2, gaussNormSq (g (mi w)) +
            2 * π * S) / 2 := by
          rw [← hSk]
          congr 2
          exact Finset.sum_congr rfl fun k _ => hlev k
  linarith

/-- **Gaussian-`L²` derivatives up to order `j` imply `f ∈ X_{G,j}`**, with
`∑_ℓ qsum j ℓ |⟪e_ℓ, f⟫|²` summable. -/
theorem summable_qsum_of_isWeakFamily {j : ℕ} {f : XG} {g : ℕ × ℕ → ℝ × ℝ → ℂ}
    (h : IsWeakFamily j (planar f) g) :
    Summable fun ℓ : ℕ => qsum j ℓ * ‖coef f ℓ‖ ^ 2 := by
  refine summable_of_sum_range_le (c := (∑ k ∈ Finset.range (j + 1),
    ∑ w : Fin k → Fin 2, gaussNormSq (g (mi w))) / (2 * π))
    (fun ℓ => mul_nonneg (qsum_nonneg j ℓ) (by positivity)) fun M => ?_
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact two_pi_sum_le h M

theorem mem_XGj_of_isWeakFamily {j : ℕ} {f : XG} {g : ℕ × ℕ → ℝ × ℝ → ℂ}
    (h : IsWeakFamily j (planar f) g) : f ∈ XGj j := by
  rw [mem_XGj_iff]
  refine Summable.of_nonneg_of_le (fun ℓ => by positivity) (fun ℓ => ?_)
    (summable_qsum_of_isWeakFamily h)
  have h1 : (1 + (ℓ : ℝ)) ^ j ≤ qsum j ℓ :=
    (qpoly_ge j ℓ).trans (Finset.single_le_sum (f := fun k => qpoly k (2 + ℓ))
      (fun k _ => qpoly_nonneg k ℓ) (Finset.mem_range.2 (Nat.lt_succ_self j)))
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

end UnforcedLeray.B0121
