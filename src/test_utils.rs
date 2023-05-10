use core::iter;

use crate::alloc::AllocationMode;

pub(crate) fn modes() -> impl Iterator<Item = AllocationMode> {
    use AllocationMode::*;
    [Constant, Input, Witness].into_iter()
}

pub(crate) fn combination<T: Clone>(
    mut i: impl Iterator<Item = T>,
) -> impl Iterator<Item = (AllocationMode, T)> {
    iter::from_fn(move || i.next().map(|t| modes().map(move |mode| (mode, t.clone()))))
        .flat_map(|x| x)
}
