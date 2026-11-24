import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_2_3

/-!
# Part II-b, task `PartII-b:T08/2/3/2` (`MollInHr`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1898-1915.
`mollInHr_of` proves `MollInHr` from three short leaves:

* `LocIntLogPull`: an `H_r` profile supported in `s ∈ [s₀, s₁]`, `s₀ > 0`, is locally integrable in
  the chart `(u, q, η)` (Hölder on the window, weight `s^{r/2-5/2}` bounded below there);
* `MollNiceGen`: mollification of an a.e. `q`-periodic, window- and `η`-cut, locally integrable
  chart profile is a nice profile (the content of `DriftMollNice` for an arbitrary profile, not only
  the first member of a pair);
* `NiceInHr`: a nice profile lies in `H_r` (continuous, periodic, bounded on the window of finite
  `hMeas`-measure).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIb

/-- **Leaf A** (SP 1898-1903).  Hölder on the window `[s₀, s₁]`, `u = log s`: the weight
`s^{r/2-5/2}` is bounded below by a positive constant, so `∫_K |f(e^u,q,η)| du dq dη` is bounded
by `C ‖f‖_{H_r}` on every compact `K` (use a.e. `q`-periodicity to pass from one cell to `K`). -/
def LocIntLogPull : Prop :=
  ∀ (c r : ℝ) (f : CProf), 0 < c → 1 < r → InHr c r f → ∀ s₀ s₁ : ℝ, 0 < s₀ → SCut s₀ s₁ f →
    LocallyIntegrable (logPull f) volume

/-- **Leaf B** (SP 1912-1915).  `ρ_n * (f∘exp)` is smooth (`HasCompactSupport.contDiff_convolution_left`),
`c`-periodic everywhere in `q` (translate the integration variable, a.e. periodicity of `f`), and
vanishes for `u` outside `[log s₀ - 1/2, log s₁ + 1/2]` and `|η| > L + 1`; `expPush` of it is smooth
because it vanishes for `s < s₀ e^{-1/2}`. -/
def MollNiceGen : Prop :=
  ∀ (c : ℝ) (f : CProf) (s₀ s₁ L : ℝ), 0 < c → 0 < s₀ → QPeriodic c f → SCut s₀ s₁ f →
    EtaCut L f → LocallyIntegrable (logPull f) volume → ∀ n : ℕ, NiceProf c (mollP n f)

/-- **Leaf C**.  A nice profile is in `H_r`: continuous hence measurable, everywhere periodic hence
a.e. periodic, bounded by its sup over one cell times the finite `hMeas`-measure of the window
`[s₀,s₁] × cell × [-L,L]` (`∫_{s₀}^{s₁} s^{r/2-5/2} ds < ∞`). -/
def NiceInHr : Prop :=
  ∀ (c r : ℝ) (g : CProf), 0 < c → NiceProf c g → InHr c r g

/-- **`MollInHr` from the three leaves.** -/
theorem mollInHr_of (h1 : LocIntLogPull) (h2 : MollNiceGen) (h3 : NiceInHr) : MollInHr := by
  intro c r b Sb hc hr hp n
  obtain ⟨⟨⟨hb, hSb, -⟩, s₀, s₁, hs₀, hbs, hSbs⟩, L, hbL, hSbL⟩ := hp
  have key : ∀ f : CProf, InHr c r f → SCut s₀ s₁ f → EtaCut L f → InHr c r (mollP n f) :=
    fun f hf hs hL =>
      h3 c r _ hc (h2 c f s₀ s₁ L hc hs₀ hf.periodic hs hL (h1 c r f hc hr hf s₀ s₁ hs₀ hs) n)
  exact ⟨key b hb hbs hbL, key Sb hSb hSbs hSbL⟩

end UnforcedLeray.Short.IIb
