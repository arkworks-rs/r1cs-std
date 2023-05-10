use crate::alloc::AllocationMode;

pub(crate) fn modes() -> impl Iterator<Item = AllocationMode> {
    [
        AllocationMode::Constant,
        AllocationMode::Input,
        AllocationMode::Witness,
    ]
    .into_iter()
}

pub(crate) fn combination<T: Clone + 'static>(
    mut iter: impl Iterator<Item = T>,
) -> impl Iterator<Item = (AllocationMode, T)> {
    core::iter::from_fn(move || {
        iter.next()
            .map(move |t| modes().map(move |mode| (mode, t.clone())))
    })
    .flat_map(|x| x)
}
