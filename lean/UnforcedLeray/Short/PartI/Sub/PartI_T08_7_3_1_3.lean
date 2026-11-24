import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_3_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundA

/-!
# Part I, task `PartI:T08/7/3/1/3` (`JTQMid`): decomposition

Source: `the November 2 reference manuscript` lines 352-358.
`JTQMid` is reduced to `MidCore`, a statement about three smooth scalar periodic functions
`g₁, g₂, g₃` (components of `∇f`, i.e. `wordComp [β] f k`): the triple integral
`∫_cell D^n g₁ · D^{l₁} g₂ · D^{l₂} g₃` with `l₁ + l₂ = n`, `l₁, l₂ ≥ 1` is bounded by `C G J`
(`G` the sup bound of the `gᵢ`, `J` a bound for the `L²` norm squared of every word of length `n`
of each `gᵢ`). `MidCore` itself is to be proved from a three-factor Hölder inequality and the
word form of `CylGN`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Admissibility of a scalar function `g` on the cell of period `c`: smooth, periodic, every word
derivative in `L²(cell)`, sup bound `G`, and `∫_cell (D_v g)² ≤ J` for every word `v` of length `n`. -/
def MidAdm (c G J : ℝ) (n : ℕ) (g : Plane → ℝ) : Prop :=
  ContDiff ℝ ∞ g ∧ Cyl.IsPeriodic c g ∧
    (∀ w : List Bool, MemLp (B0151.derivWord w g) 2 (Cyl.cellμ c)) ∧ (∀ z, |g z| ≤ G) ∧
    ∀ v : List Bool, v.length = n →
      ∫ z in Cyl.cell c, B0151.derivWord v g z * B0151.derivWord v g z ≤ J

/-- **Leaf `MidCore`** (lines 352-358): for `n ≥ 2` there is `C ≥ 0`, depending only on `n`, such
that for all `c ≥ 1`, admissible `g₁, g₂, g₃` (sup bound `G`, word `L²` bound `J` at order `n`),
`l₁, l₂ ≥ 1` with `l₁ + l₂ = n` and words `u₁, u₂, u₃` of lengths `n, l₁, l₂`,
`|∫_cell D_{u₁} g₁ · (D_{u₂} g₂ · D_{u₃} g₃)| ≤ C G J`. Route: Hölder with exponents
`2n/l₁`, `2n/l₂`, `2` (reciprocals add to `1`), the period-independent Gagliardo-Nirenberg
`‖D^l g‖_{2n/l} ≤ C ‖g‖_∞^{1-l/n} ‖D^n g‖₂^{l/n}` (`CylGN`) for `g₂, g₃`, powers of `G` add to
`1` and powers of `J` add to `1`. -/
def MidCore : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ (g₁ g₂ g₃ : Plane → ℝ) (G J : ℝ),
    0 ≤ G → 0 ≤ J → MidAdm c G J n g₁ → MidAdm c G J n g₂ → MidAdm c G J n g₃ →
    ∀ l₁ l₂ : ℕ, 1 ≤ l₁ → 1 ≤ l₂ → l₁ + l₂ = n →
      ∀ u₁ u₂ u₃ : List Bool, u₁.length = n → u₂.length = l₁ → u₃.length = l₂ →
        |∫ z in Cyl.cell c, B0151.derivWord u₁ g₁ z *
          (B0151.derivWord u₂ g₂ z * B0151.derivWord u₃ g₃ z)| ≤ C * (G * J)

theorem wc_append (u : List Bool) (b : Bool) (f : Plane → Vec) (k : Fin 2) :
    wordComp (u ++ [b]) f k = B0151.derivWord u (wordComp [b] f k) :=
  vjl_derivWord_append b _ u

theorem midAdm_comp {c : ℝ} {f : Plane → Vec} (hf : CellSmoothL2 c f) {G : ℝ}
    (hG : ∀ (β : Bool) (k : Fin 2) (z : Plane), |wordComp [β] f k z| ≤ G) (n : ℕ) (b : Bool)
    (k : Fin 2) : MidAdm c G (jetEnergy c (n + 1) f) n (wordComp [b] f k) := by
  refine ⟨contDiff_wordComp hf.1 [b] k, ?_, ?_, hG b k, ?_⟩
  · exact ForcingIBP.per_derivWord [b] _ (hf.2.1.fun_comp (fun x => x k))
  · intro w
    rw [← wc_append]
    exact hf.2.2 _ k
  · intro v hv
    have := ba_single_le hf (v ++ [b]) k
    rw [wc_append] at this
    simpa [hv] using this

theorem jtQMid_proof_of (h : MidCore) : JTQMid := by
  intro j
  by_cases hj : 3 ≤ j
  · obtain ⟨C, hC, hM⟩ := h (j - 1) (by omega)
    refine ⟨C, hC, ?_⟩
    intro c V f G M H w hw p hp h2 h3 m k
    obtain ⟨hc, hV, hVp, hVd, hf, hfd, hfb, hG, hMb⟩ := H
    have hG0 : 0 ≤ G := le_trans (abs_nonneg _) (hG true 0 0)
    have hJ0 : 0 ≤ jetEnergy c j f := jetEnergy_nonneg c j f
    have hwl := mem_wordsOfLength_length hw
    have hlen := wac_splits_len_sum w p hp
    have hw0 : w ≠ [] := by
      intro h0; subst h0; simp at hwl; omega
    have hp0 : p.1 ≠ [] := by
      intro h0; rw [h0] at h2; simp at h2
    obtain ⟨β₁, hβ₁⟩ : ∃ β, w = w.dropLast ++ [β] :=
      ⟨w.getLast hw0, (List.dropLast_append_getLast hw0).symm⟩
    obtain ⟨β₂, hβ₂⟩ : ∃ β, p.1 = p.1.dropLast ++ [β] :=
      ⟨p.1.getLast hp0, (List.dropLast_append_getLast hp0).symm⟩
    have hjj : j - 1 + 1 = j := by omega
    have a1 := midAdm_comp hf hG (j - 1) β₁ k
    have a2 := midAdm_comp hf hG (j - 1) β₂ m
    have a3 := midAdm_comp hf hG (j - 1) (dirOf m) k
    rw [hjj] at a1 a2 a3
    have e1 : wordComp w f k = B0151.derivWord w.dropLast (wordComp [β₁] f k) := by
      rw [← wc_append, ← hβ₁]
    have e2 : wordComp p.1 f m = B0151.derivWord p.1.dropLast (wordComp [β₂] f m) := by
      rw [← wc_append, ← hβ₂]
    have e3 : wordComp (p.2 ++ [dirOf m]) f k =
        B0151.derivWord p.2 (wordComp [dirOf m] f k) := wc_append _ _ _ _
    have := hM c hc _ _ _ G (jetEnergy c j f) hG0 hJ0 a1 a2 a3 (p.1.length - 1) p.2.length
      (by omega) (by omega) (by omega) w.dropLast p.1.dropLast p.2
      (by simp; omega) (by simp) rfl
    rw [e1, e2, e3]
    exact this
  · refine ⟨0, le_refl _, ?_⟩
    intro c V f G M H w hw p hp h2 h3 m k
    omega
/-- **Leaf `MidHolder3`** (lines 352-358): three-factor Hölder on the cell. For real `p, q > 1` with
`1/p + 1/q + 1/2 = 1`, `a ∈ L²`, `b ∈ L^p`, `d ∈ L^q` on `Cyl.cellμ c`:
`|∫_cell a (b d)| ≤ (∫ a²)^{1/2} (∫ |b|^p)^{1/p} (∫ |d|^q)^{1/q}`. Route: Mathlib
`MeasureTheory.integral_mul_le_Lp_mul_Lq` (or the `lintegral_` / `eLpNorm` form, with
`MemLp.mul` / `MemLp.integrable_mul`) applied twice, with the intermediate exponent `r` with
`1/r = 1/p + 1/q`. -/
def MidHolder3 : Prop :=
  ∀ (c : ℝ) (a b d : Plane → ℝ) (p q : ℝ), 1 < p → 1 < q → 1 / p + 1 / q + 1 / 2 = 1 →
    MemLp a 2 (Cyl.cellμ c) → MemLp b (ENNReal.ofReal p) (Cyl.cellμ c) →
    MemLp d (ENNReal.ofReal q) (Cyl.cellμ c) →
      |∫ z in Cyl.cell c, a z * (b z * d z)| ≤
        (∫ z in Cyl.cell c, a z * a z) ^ (1 / 2 : ℝ) *
          (∫ z in Cyl.cell c, |b z| ^ p) ^ (1 / p) * (∫ z in Cyl.cell c, |d z| ^ q) ^ (1 / q)

/-- **Leaf `MidGNWord`** (lines 355-357; `CylGN` of `Sub/T07.lean`, `cylJetWord_proof`,
`cylDerivFinite_proof`): the period-independent Gagliardo-Nirenberg inequality in word form. For
`n ≥ 1` there is `C ≥ 0` (depending only on `n`) such that for `c ≥ 1`, `g` admissible with sup bound
`S` and word bound `J` at order `n` (`MidAdm c S J n g`), `1 ≤ l ≤ n` and any word `u` of length `l`,
`(∫_cell |D_u g|^{2n/l})^{l/(2n)} ≤ C S^{1-l/n} J^{l/(2n)}`. Route: `CylGN` for `g` gives the
`eLpNorm` bound of `jet l g` with `cellL2 (jet n g)`; `|D_u g| ≤ ‖jet l g‖` and
`‖jet n g‖ ≤ ∑_{|v|=n} |D_v g|` (`cylJetWord_proof`), so `cellL2 (jet n g) ≤ 2^n J^{1/2}`
(Minkowski over the `2^n` words), `⨆ ‖g‖ₑ ≤ S`; convert `eLpNorm` to the real integral. -/
def MidGNWord : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ (g : Plane → ℝ) (S J : ℝ),
    0 ≤ S → 0 ≤ J → MidAdm c S J n g → ∀ l : ℕ, 1 ≤ l → l ≤ n → ∀ u : List Bool, u.length = l →
      (∫ z in Cyl.cell c, |B0151.derivWord u g z| ^ (2 * (n : ℝ) / l)) ^ ((l : ℝ) / (2 * n)) ≤
        C * (S ^ (1 - (l : ℝ) / n) * J ^ ((l : ℝ) / (2 * n)))

/-- (Doc only.) `MidCore` follows from `MidHolder3` and `MidGNWord` (exponent bookkeeping: with `p = 2n/l₁`, `q = 2n/l₂`, `1/p + 1/q + 1/2 = (l₁ + l₂)/(2n) + 1/2 = 1`; the first factor gives
`J^{1/2}`; powers of `S = G`: `(1 - l₁/n) + (1 - l₂/n) = 1`; powers of `J`:
`1/2 + l₁/(2n) + l₂/(2n) = 1`). -/
theorem midCoreFromDoc : True := trivial

end UnforcedLeray.Short.PartI
