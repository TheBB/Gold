// Boxable
// ----------------------------------------------------------------

pub trait Boxable<T> where T: Sized {
    fn to_box(self) -> Box<T>;
}

impl<T> Boxable<T> for Box<T> {
    fn to_box(self) -> Box<T> { self }
}

impl<T> Boxable<T> for T {
    fn to_box(self) -> Box<T> { Box::new(self) }
}


// Splattable
// ----------------------------------------------------------------

pub struct Splat<T> {
    pub object: T
}

pub trait Splattable<T> {
    fn splat(&self) -> Splat<T>;
}
