import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyCalculus.Framework

/-!
# Helper for `PartII-a:R01`, target `earlyCalculus`: closure of `EarlyBdd` (linear fields)

Helpers for `Tasks/R01/EarlyCalculus.lean`: `EarlyBdd` is closed under sums, constant multiples,
multiplication by `ν`, negation, difference, and the derivatives `∂_q`, `∂_η`, `∂_s` (the
derivatives are read off from the jets of order one higher, after commuting the three
commuting derivatives on the `C^∞` profiles of `{s > 0}`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.EarlyCalc

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

theorem polyConst_smul_le {k C C' : ℝ} {d : ℕ} {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (hk : 0 ≤ k) (hCC : C ≤ C') : k * polyConst C d ν c ≤ polyConst (k * C') d ν c := by
  unfold polyConst
  have hP : 0 ≤ (1 + c + ν⁻¹) ^ d := pow_nonneg (by linarith [inv_pos.2 hν]) d
  calc k * (C * (1 + c + ν⁻¹) ^ d) ≤ k * (C' * (1 + c + ν⁻¹) ^ d) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCC hP) hk
    _ = k * C' * (1 + c + ν⁻¹) ^ d := by ring

theorem earlyBdd_add {ρ : ℝ} {X Y : ProfFam} (hX : EarlyBdd ρ X) (hY : EarlyBdd ρ Y) :
    EarlyBdd ρ (fun ν ψ p => X ν ψ p + Y ν ψ p) := by
  unfold EarlyBdd at hX hY ⊢
  refine ⟨fun ν hν ψ p hψ => (hX.1 ν hν ψ p hψ).add (hY.1 ν hν ψ p hψ), fun m a b ℓ => ?_⟩
  obtain ⟨ν₁, C₁, d₁, hν₁, H₁⟩ := hX.2 m a b ℓ
  obtain ⟨ν₂, C₂, d₂, hν₂, H₂⟩ := hY.2 m a b ℓ
  refine ⟨min ν₁ ν₂, max C₁ 0 + max C₂ 0, max d₁ d₂, lt_min hν₁ hν₂,
    fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hνX : ν ∈ Ioo 0 ν₁ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
  have hνY : ν ∈ Ioo 0 ν₂ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
  have hEq := jet_add ℓ a b (hX.1 ν hν0 ψ p hψ) (hY.1 ν hν0 ψ p hψ)
  have t1 : (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x| ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) :=
    H₁ ν hνX ψ p hψ x hx0 hx1
  have t2 : (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (Y ν ψ p) x| ≤ polyConst C₂ d₂ ν (ν ^ (-ρ)) :=
    H₂ ν hνY ψ p hψ x hx0 hx1
  have hw : 0 ≤ (1 + x.2.1 ^ 2) ^ m := by positivity
  show (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (fun y => X ν ψ p y + Y ν ψ p y) x| ≤ _
  rw [hEq (show x ∈ AgeSet from hx0)]
  dsimp only
  calc (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x + jet ℓ a b (Y ν ψ p) x|
      ≤ (1 + x.2.1 ^ 2) ^ m * (|jet ℓ a b (X ν ψ p) x| + |jet ℓ a b (Y ν ψ p) x|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
    _ = (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x| +
          (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (Y ν ψ p) x| := by ring
    _ ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) + polyConst C₂ d₂ ν (ν ^ (-ρ)) := add_le_add t1 t2
    _ ≤ _ := polyConst_add_le hν0 hc

theorem earlyBdd_constMul {ρ : ℝ} (r : ℝ) {X : ProfFam} (hX : EarlyBdd ρ X) :
    EarlyBdd ρ (fun ν ψ p x => r * X ν ψ p x) := by
  unfold EarlyBdd at hX ⊢
  refine ⟨fun ν hν ψ p hψ => (contDiffOn_const (c := r)).mul (hX.1 ν hν ψ p hψ),
    fun m a b ℓ => ?_⟩
  obtain ⟨ν₀, C, d, hν₀, H⟩ := hX.2 m a b ℓ
  refine ⟨ν₀, |r| * max C 0, d, hν₀, fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hJ := jet_const ℓ a b r (hX.1 ν hν0 ψ p hψ)
  have t : (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x| ≤ polyConst C d ν (ν ^ (-ρ)) :=
    H ν hν ψ p hψ x hx0 hx1
  show (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (fun y => r * X ν ψ p y) x| ≤ _
  rw [hJ (show x ∈ AgeSet from hx0)]
  dsimp only
  calc (1 + x.2.1 ^ 2) ^ m * |r * jet ℓ a b (X ν ψ p) x|
      = |r| * ((1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x|) := by
        rw [abs_mul]
        ring
    _ ≤ |r| * polyConst C d ν (ν ^ (-ρ)) := mul_le_mul_of_nonneg_left t (abs_nonneg r)
    _ ≤ polyConst (|r| * max C 0) d ν (ν ^ (-ρ)) :=
        polyConst_smul_le hν0 hc (abs_nonneg r) (le_max_left C 0)

theorem earlyBdd_nuMul {ρ : ℝ} {X : ProfFam} (h : EarlyBdd ρ X) :
    EarlyBdd ρ (fun ν ψ p x => ν * X ν ψ p x) := by
  unfold EarlyBdd at h ⊢
  refine ⟨fun ν hν ψ p hψ => (contDiffOn_const (c := ν)).mul (h.1 ν hν ψ p hψ),
    fun m a b ℓ => ?_⟩
  obtain ⟨ν₀, C, d, hν₀, H⟩ := h.2 m a b ℓ
  refine ⟨min ν₀ 1, max C 0, d, lt_min hν₀ one_pos, fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := (lt_of_lt_of_le hν.2 (min_le_right _ _)).le
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hνX : ν ∈ Ioo 0 ν₀ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
  have hJ := jet_const ℓ a b ν (h.1 ν hν0 ψ p hψ)
  have t : (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x| ≤ polyConst C d ν (ν ^ (-ρ)) :=
    H ν hνX ψ p hψ x hx0 hx1
  have hw : 0 ≤ (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x| :=
    mul_nonneg (by positivity) (abs_nonneg _)
  show (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (fun y => ν * X ν ψ p y) x| ≤ _
  rw [hJ (show x ∈ AgeSet from hx0)]
  dsimp only
  calc (1 + x.2.1 ^ 2) ^ m * |ν * jet ℓ a b (X ν ψ p) x|
      = ν * ((1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x|) := by
        rw [abs_mul, abs_of_pos hν0]
        ring
    _ ≤ 1 * ((1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x|) :=
        mul_le_mul_of_nonneg_right hν1 hw
    _ ≤ polyConst C d ν (ν ^ (-ρ)) := by linarith
    _ ≤ polyConst (max C 0) d ν (ν ^ (-ρ)) :=
        polyConst_mono hν0 hc (le_max_left C 0) (le_max_right C 0) le_rfl

theorem earlyBdd_dQ {ρ : ℝ} {X : ProfFam} (h : EarlyBdd ρ X) :
    EarlyBdd ρ (fun ν ψ p => partialQ (X ν ψ p)) := by
  unfold EarlyBdd at h ⊢
  refine ⟨fun ν hν ψ p hψ => smooth_Dir eqDir (h.1 ν hν ψ p hψ), fun m a b ℓ => ?_⟩
  obtain ⟨ν₀, C, d, hν₀, H⟩ := h.2 m a (b + 1) ℓ
  refine ⟨ν₀, C, d, hν₀, fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
  exact H ν hν ψ p hψ x hx0 hx1

theorem earlyBdd_dEta {ρ : ℝ} {X : ProfFam} (h : EarlyBdd ρ X) :
    EarlyBdd ρ (fun ν ψ p => partialEta (X ν ψ p)) := by
  unfold EarlyBdd at h ⊢
  refine ⟨fun ν hν ψ p hψ => smooth_Dir eηDir (h.1 ν hν ψ p hψ), fun m a b ℓ => ?_⟩
  obtain ⟨ν₀, C, d, hν₀, H⟩ := h.2 m (a + 1) b ℓ
  refine ⟨ν₀, C, d, hν₀, fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
  have hG := h.1 ν hν.1 ψ p hψ
  have hjet : EqOn (jet ℓ a b (Dir eηDir (X ν ψ p))) (jet ℓ (a + 1) b (X ν ψ p)) AgeSet := by
    have e1 := iter_comm eqDir eηDir b hG
    have e2 := iter_congr eηDir a e1
    have e3 : EqOn ((Dir eηDir)^[a] (Dir eηDir ((Dir eqDir)^[b] (X ν ψ p))))
        ((Dir eηDir)^[a + 1] ((Dir eqDir)^[b] (X ν ψ p))) AgeSet :=
      fun x _ => congrFun (Function.iterate_succ_apply _ _ _).symm x
    have e4 := iter_congr esDir ℓ (e2.trans e3)
    exact e4
  show (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (Dir eηDir (X ν ψ p)) x| ≤ _
  rw [hjet (show x ∈ AgeSet from hx0)]
  exact H ν hν ψ p hψ x hx0 hx1

theorem earlyBdd_dAge {ρ : ℝ} {X : ProfFam} (h : EarlyBdd ρ X) :
    EarlyBdd ρ (fun ν ψ p => partialAge (X ν ψ p)) := by
  unfold EarlyBdd at h ⊢
  refine ⟨fun ν hν ψ p hψ => smooth_Dir esDir (h.1 ν hν ψ p hψ), fun m a b ℓ => ?_⟩
  obtain ⟨ν₀, C, d, hν₀, H⟩ := h.2 m a b (ℓ + 1)
  refine ⟨ν₀, C, d, hν₀, fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
  have hG := h.1 ν hν.1 ψ p hψ
  have hjet : EqOn (jet ℓ a b (Dir esDir (X ν ψ p))) (jet (ℓ + 1) a b (X ν ψ p)) AgeSet := by
    have f1 := iter_comm eqDir esDir b hG
    have f2 := iter_congr eηDir a f1
    have f3 := iter_comm eηDir esDir a (smooth_iter eqDir b hG)
    have f4 := iter_congr esDir ℓ (f2.trans f3)
    have f5 : EqOn ((Dir esDir)^[ℓ] (Dir esDir ((Dir eηDir)^[a] ((Dir eqDir)^[b] (X ν ψ p)))))
        ((Dir esDir)^[ℓ + 1] ((Dir eηDir)^[a] ((Dir eqDir)^[b] (X ν ψ p)))) AgeSet :=
      fun x _ => congrFun (Function.iterate_succ_apply _ _ _).symm x
    exact f4.trans f5
  show (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (Dir esDir (X ν ψ p)) x| ≤ _
  rw [hjet (show x ∈ AgeSet from hx0)]
  exact H ν hν ψ p hψ x hx0 hx1

theorem earlyBdd_neg {ρ : ℝ} {X : ProfFam} (h : EarlyBdd ρ X) :
    EarlyBdd ρ (fun ν ψ p => -X ν ψ p) :=
  earlyBdd_congr (fun ν ψ p x => by simp only [Pi.neg_apply]; ring) (earlyBdd_constMul (-1) h)

theorem earlyBdd_sub {ρ : ℝ} {X Y : ProfFam} (hX : EarlyBdd ρ X) (hY : EarlyBdd ρ Y) :
    EarlyBdd ρ (fun ν ψ p => X ν ψ p - Y ν ψ p) :=
  earlyBdd_congr (fun ν ψ p x => by simp only [Pi.add_apply, Pi.sub_apply]; ring)
    (earlyBdd_add hX (earlyBdd_constMul (-1) hY))

end UnforcedLeray.Short.PartIIa.EarlyCalc
