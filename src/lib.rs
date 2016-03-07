use std::borrow::Borrow;
use std::hash::{Hash, BuildHasher};
use std::iter;
use std::marker::PhantomData;
use std::collections::HashMap;
use std::collections::hash_map::{Iter, IterMut};

/// A type which can be split into disjoint references. SplitType allows a type to be split multiple
// ways.
pub trait Splittable<SplitType = ()> {
    type A;
    type B;
    fn split(&self) -> (&Self::A, &Self::B);
    fn split_mut(&mut self) -> (&mut Self::A, &mut Self::B);
}

/// Splits a `HashMap` into two disjoint hashmap references, able to access the split parts of the
/// stored `Splittable` values independently.
pub fn split<'a, K: 'a, V: 'a, S, SplitType>(v: &'a mut HashMap<K, V, S>) -> (HashMapA<'a, K, V, S, SplitType>, HashMapB<'a, K, V, S, SplitType>)
where K: Eq + Hash, S: BuildHasher, V: Splittable<SplitType> {
    let b = v as * mut _;
    let b = unsafe { &mut*b };
    (HashMapA(PhantomData, v), HashMapB(PhantomData, b))
}

// .d8888. d8888b. db      d888888b d888888b       .d8b.
// 88'  YP 88  `8D 88        `88'   `~~88~~'      d8' `8b
// `8bo.   88oodD' 88         88       88         88ooo88
//   `Y8b. 88~~~   88         88       88         88~~~88
// db   8D 88      88booo.   .88.      88         88   88
// `8888Y' 88      Y88888P Y888888P    YP         YP   YP

fn iter_a_helper<'a, K: 'a, V: 'a, SplitType>((k, v): (&'a K, &'a V)) -> (&'a K, &'a <V as Splittable<SplitType>>::A)
where V: Splittable<SplitType>,
<V as Splittable<SplitType>>::A: 'a,
<V as Splittable<SplitType>>::B: 'a {
    (k, v.split().0)
}

fn iter_mut_a_helper<'a, K: 'a, V: 'a, SplitType>((k, v): (&'a K, &'a mut V)) -> (&'a K, &'a mut <V as Splittable<SplitType>>::A)
where V: Splittable<SplitType>,
<V as Splittable<SplitType>>::A: 'a,
<V as Splittable<SplitType>>::B: 'a {
    (k, v.split_mut().0)
}

/// A wrapper around a HashMap which provides access to the A portion of a `Splittable` value type
pub struct HashMapA<'a, K: 'a, V: 'a, S: 'a, SplitType>(PhantomData<SplitType>, &'a mut HashMap<K, V, S>)
where K: Eq + Hash, S: BuildHasher, V: Splittable<SplitType>;

impl <'a, K: 'a, V: 'a, S, SplitType> HashMapA<'a, K, V, S, SplitType>
where K: Eq + Hash, S: BuildHasher, V: Splittable<SplitType> {
    /// An iterator visiting all key-value pairs in arbitrary order. Iterator element type is
    /// `(&'b K, &'b V::A)`.
    pub fn iter<'b>(&'b self) -> iter::Map<
        Iter<'b, K, V>,
        fn((&'b K, &'b V)) -> (&'b K, &'b <V as Splittable<SplitType>>::A),
    >
    where 'a: 'b {
        self.1.iter().map(iter_a_helper::<'b, K, V, SplitType>)
    }

    /// An iterator visiting all key-value pairs in arbitrary order. Iterator element type is
    /// `(&'b K, &'b mut V::A)`.
    pub fn iter_mut<'b>(&'b mut self) -> iter::Map<
        IterMut<'b, K, V>,
        fn((&'b K, &'b mut V)) -> (&'b K, &'b mut <V as Splittable<SplitType>>::A),
    > {
        self.1.iter_mut().map(iter_mut_a_helper::<'b, K, V, SplitType>)
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the HashMap<K, V> might be able to hold more, but is
    /// guaranteed to be able to hold at least this many.
    pub fn capacity(&self) -> usize { self.1.capacity() }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize { self.1.len() }

    /// Returns true if the map contains no elements.
    pub fn is_empty(&self) -> bool { self.1.is_empty() }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form must match those for the key type.
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&<V as Splittable<SplitType>>::A>
    where Q: Hash + Eq, K: Borrow<Q> {
        self.1.get(k).map(|v| v.split().0)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form must match those for the key type.
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut <V as Splittable<SplitType>>::A>
    where Q: Hash + Eq, K: Borrow<Q> {
        self.1.get_mut(k).map(|v| v.split_mut().0)
    }
}

// .d8888. d8888b. db      d888888b d888888b      d8888b.
// 88'  YP 88  `8D 88        `88'   `~~88~~'      88  `8D
// `8bo.   88oodD' 88         88       88         88oooY'
//   `Y8b. 88~~~   88         88       88         88~~~b.
// db   8D 88      88booo.   .88.      88         88   8D
// `8888Y' 88      Y88888P Y888888P    YP         Y8888P'

fn iter_b_helper<'a, K: 'a, V: 'a, SplitType>((k, v): (&'a K, &'a V)) -> (&'a K, &'a <V as Splittable<SplitType>>::B)
where V: Splittable<SplitType>,
<V as Splittable<SplitType>>::A: 'a,
<V as Splittable<SplitType>>::B: 'a {
    (k, v.split().1)
}

fn iter_mut_b_helper<'a, K: 'a, V: 'a, SplitType>((k, v): (&'a K, &'a mut V)) -> (&'a K, &'a mut <V as Splittable<SplitType>>::B)
where V: Splittable<SplitType>,
<V as Splittable<SplitType>>::A: 'a,
<V as Splittable<SplitType>>::B: 'a {
    (k, v.split_mut().1)
}

/// A wrapper around a HashMap which provides access to the B portion of a `Splittable` value type
pub struct HashMapB<'a, K: 'a, V: 'a, S: 'a, SplitType>(PhantomData<SplitType>, &'a mut HashMap<K, V, S>)
where K: Eq + Hash, S: BuildHasher, V: Splittable<SplitType>;

impl <'a, K: 'a, V: 'a, S, SplitType> HashMapB<'a, K, V, S, SplitType>
where K: Eq + Hash, S: BuildHasher, V: Splittable<SplitType> {
    /// An iterator visiting all key-value pairs in arbitrary order. Iterator element type is
    /// `(&'b K, &'b V::B)`.
    pub fn iter<'b>(&'b self) -> iter::Map<
        Iter<'b, K, V>,
        fn((&'b K, &'b V)) -> (&'b K, &'b <V as Splittable<SplitType>>::B),
    >
    where 'a: 'b {
        self.1.iter().map(iter_b_helper::<'b, K, V, SplitType>)
    }

    /// An iterator visiting all key-value pairs in arbitrary order. Iterator element type is
    /// `(&'b K, &'b mut V::B)`.
    pub fn iter_mut<'b>(&'b mut self) -> iter::Map<
        IterMut<'b, K, V>,
        fn((&'b K, &'b mut V)) -> (&'b K, &'b mut <V as Splittable<SplitType>>::B),
    > {
        self.1.iter_mut().map(iter_mut_b_helper::<'b, K, V, SplitType>)
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the HashMap<K, V> might be able to hold more, but is
    /// guaranteed to be able to hold at least this many.
    pub fn capacity(&self) -> usize { self.1.capacity() }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize { self.1.len() }

    /// Returns true if the map contains no elements.
    pub fn is_empty(&self) -> bool { self.1.is_empty() }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form must match those for the key type.
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&<V as Splittable<SplitType>>::B>
    where Q: Hash + Eq, K: Borrow<Q> {
        self.1.get(k).map(|v| v.split().1)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form must match those for the key type.
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut <V as Splittable<SplitType>>::B>
    where Q: Hash + Eq, K: Borrow<Q> {
        self.1.get_mut(k).map(|v| v.split_mut().1)
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use super::*;

    #[derive(Clone, Copy, PartialEq, Debug)]
    struct Pair {
        a: i32,
        b: f32,
    }

    impl Splittable for Pair {
        type A = i32;
        type B = f32;
        fn split(&self) -> (&Self::A, &Self::B) { (&self.a, &self.b) }
        fn split_mut(&mut self) -> (&mut Self::A, &mut Self::B) { (&mut self.a, &mut self.b) }
    }

    #[test]
    fn it_works() {
        let mut h = HashMap::new();
        h.insert(0i32, Pair{a: 1, b: 15.0});
        h.insert(1i32, Pair{a: 3, b: 14.0});
        h.insert(2i32, Pair{a: 0, b: 13.0});
        h.insert(3i32, Pair{a: 2, b: 12.0});

        {
            let (mut a, b) = split(&mut h);
            for (_, v) in a.iter_mut() {
                if let Some(b) = b.get(v) {
                    *v = *b as i32;
                }
            }
        }

        let mut result = HashMap::new();
        result.insert(0i32, Pair{a: 14, b: 15.0});
        result.insert(1i32, Pair{a: 12, b: 14.0});
        result.insert(2i32, Pair{a: 15, b: 13.0});
        result.insert(3i32, Pair{a: 13, b: 12.0});
        assert_eq!(h, result);

    }
}
