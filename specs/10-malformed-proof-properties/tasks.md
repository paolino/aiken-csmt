# Tasks

## inclusion-soundness
- [x] inclusion-soundness-properties (has-rejects-wrong-value, has-rejects-absent-key, has-rejects-other-length-key, removal-rejects-false-membership)
- [x] inclusion-range-checks with failing cases kept

## exclusion-soundness
- [x] exclusion-soundness-properties (miss-rejects-held-key, insert-rejects-held-key, push-rejects-held-key)
- [x] exclusion-range-checks with failing cases kept

## relaxation-check
- [x] planted relaxations killed in CI (range-check-kills-relaxation)
- [x] fixed case count in CI (case-count-recorded)

## honest-completeness
- [ ] random-tree vectors from haskell-mts
- [ ] honest-proofs-accepted properties

## cost-measurement
- [ ] cost table at 1, 10, 1 000, 100 000 keys, before and after

## release
- [ ] version bump and tag
