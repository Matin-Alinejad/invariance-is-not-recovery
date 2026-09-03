import Mathlib
import RecoveryFormal.SelectedMeasureConstruction
import RecoveryFormal.RetainedCountConcentration

/-!
# Retained-row thinning proof architecture

This module contains the object layer and proof decomposition used by the
completed retained-row results. The modules establish the required lemmas in this
order, either here or in separate subsequent modules:

1. `retainedNumerator_univ` and `discardedNumerator_univ`.
2. `markedRowLaw_isProbability`.
3. One-row retained/discarded cylinder identities.
4. Finite-product rectangle formula for a deterministic pattern `I`.
5. Exact pattern probability `q^|I|(1-q)^(n-|I|)` and positivity.
6. Conditional product law given `retainedSet = I`.
7. Order-preserving reindexing `Fin I.card ≃ I`.
8. Mixture over all `I.card = m`, giving the product law conditional on count.
9. Binomial count, preferably by instantiating the retained-count concentration result after indicator independence.
10. the Gaussian selected-law corollary.

The exact exported theorem contracts are in the exported theorem interfaces.  Do not
replace full measure equality by exchangeability, pairwise independence, or a
cylinder identity without the full measure-extensionality step.
-/

namespace RecoveryFormal
namespace ConditionalThinning

-- This module records definitions and proof architecture only.

end ConditionalThinning
end RecoveryFormal
