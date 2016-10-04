use std::borrow::Borrow;
use std::hash::{Hash, BuildHasher};
use std::iter;
use std::marker::PhantomData;
use std::collections::HashMap;
use std::collections::hash_map::{Iter, IterMut};

/// A type which can be split into disjoint references. SplitType allows a type to be split multiple
// ways.
pub trait Splittable<'a, SplitType = ()> {
    type A: 'a;
    type B: 'a;

    fn split(&'a self) -> (&'a Self::A, &'a Self::B);
    fn split_mut(&'a mut self) -> (&'a mut Self::A, &'a mut Self::B);
}

include!(concat!(env!("OUT_DIR"), "/splittable.rs"));


// iter a helper
fn iter_a_helper<'a, K: 'a, V: 'a, SplitType>((k, v): (&'a K, &'a V)) -> (&'a K, &'a <V as Splittable<'a, SplitType>>::A)
where V: Splittable<'a, SplitType> {
    (k, v.split().0)
}
fn iter_mut_a_helper<'a, K: 'a, V: 'a, SplitType>((k, v): (&'a K, &'a mut V)) -> (&'a K, &'a mut <V as Splittable<'a, SplitType>>::A)
where V: Splittable<'a, SplitType> {
    (k, v.split_mut().0)
}

fn iter_b_helper<'a, K: 'a, V: 'a, SplitType>((k, v): (&'a K, &'a V)) -> (&'a K, &'a <V as Splittable<'a, SplitType>>::B)
where V: Splittable<'a, SplitType> {
    (k, v.split().1)
}

fn iter_mut_b_helper<'a, K: 'a, V: 'a, SplitType>((k, v): (&'a K, &'a mut V)) -> (&'a K, &'a mut <V as Splittable<'a, SplitType>>::B)
where V: Splittable<'a, SplitType> {
    (k, v.split_mut().1)
}

include!(concat!(env!("OUT_DIR"), "/helpers.rs"));


/// A wrapper around a HashMap which provides access to the A portion of a `Splittable` value type
pub struct HashMapA<'a, K: 'a, V: 'a, S: 'a, SplitType>(PhantomData<SplitType>, &'a mut HashMap<K, V, S>)
where K: Eq + Hash, S: BuildHasher;

/// A wrapper around a HashMap which provides access to the B portion of a `Splittable` value type
pub struct HashMapB<'a, K: 'a, V: 'a, S: 'a, SplitType>(PhantomData<SplitType>, &'a mut HashMap<K, V, S>)
where K: Eq + Hash, S: BuildHasher;

include!(concat!(env!("OUT_DIR"), "/structs.rs"));


impl <'a, K: 'a, V: 'a, S, SplitType> HashMapA<'a, K, V, S, SplitType>
where K: Eq + Hash, S: BuildHasher {
    /// An iterator visiting all key-value pairs in arbitrary order. Iterator element type is
    /// `(&'b K, &'b V::A)`.
    pub fn iter<'b>(&'b self) -> iter::Map<
        Iter<'b, K, V>,
        fn((&'b K, &'b V)) -> (&'b K, &'b <V as Splittable<'b, SplitType>>::A),
    >
    where V: Splittable<'b, SplitType> {
        self.1.iter().map(iter_a_helper::<'b, K, V, SplitType>)
    }

    /// An iterator visiting all key-value pairs in arbitrary order. Iterator element type is
    /// `(&'b K, &'b mut V::A)`.
    pub fn iter_mut<'b>(&'b mut self) -> iter::Map<
        IterMut<'b, K, V>,
        fn((&'b K, &'b mut V)) -> (&'b K, &'b mut <V as Splittable<'b, SplitType>>::A),
    >
    where V: Splittable<'b, SplitType>
        {
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
    pub fn get<'b, Q: ?Sized>(&'b self, k: &Q) -> Option<&'b <V as Splittable<'b, SplitType>>::A>
    where Q: Hash + Eq, K: Borrow<Q>, V: Splittable<'b, SplitType> {
        self.1.get(k).map(|v| v.split().0)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form must match those for the key type.
    pub fn get_mut<'b, Q: ?Sized>(&'b mut self, k: &Q) -> Option<&'b mut <V as Splittable<'b, SplitType>>::A>
    where Q: Hash + Eq, K: Borrow<Q>, V: Splittable<'b, SplitType> {
        self.1.get_mut(k).map(|v| v.split_mut().0)
    }
}

impl <'a, K: 'a, V: 'a, S, SplitType> HashMapB<'a, K, V, S, SplitType>
where K: Eq + Hash, S: BuildHasher {
    /// An iterator visiting all key-value pairs in arbitrary order. Iterator element type is
    /// `(&'b K, &'b V::B)`.
    pub fn iter<'b>(&'b self) -> iter::Map<
        Iter<'b, K, V>,
        fn((&'b K, &'b V)) -> (&'b K, &'b <V as Splittable<'b, SplitType>>::B),
    >
    where V: Splittable<'b, SplitType> {
        self.1.iter().map(iter_b_helper::<'b, K, V, SplitType>)
    }

    /// An iterator visiting all key-value pairs in arbitrary order. Iterator element type is
    /// `(&'b K, &'b mut V::B)`.
    pub fn iter_mut<'b>(&'b mut self) -> iter::Map<
        IterMut<'b, K, V>,
        fn((&'b K, &'b mut V)) -> (&'b K, &'b mut <V as Splittable<'b, SplitType>>::B),
    >
    where V: Splittable<'b, SplitType>
        {
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
    pub fn get<'b, Q: ?Sized>(&'b self, k: &Q) -> Option<&'b <V as Splittable<'b, SplitType>>::B>
    where Q: Hash + Eq, K: Borrow<Q>, V: Splittable<'b, SplitType> {
        self.1.get(k).map(|v| v.split().1)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form must match those for the key type.
    pub fn get_mut<'b, Q: ?Sized>(&'b mut self, k: &Q) -> Option<&'b mut <V as Splittable<'b, SplitType>>::B>
    where Q: Hash + Eq, K: Borrow<Q>, V: Splittable<'b, SplitType> {
        self.1.get_mut(k).map(|v| v.split_mut().1)
    }
}

include!(concat!(env!("OUT_DIR"), "/impls.rs"));


/// Splits a `HashMap` into two disjoint hashmap references, able to access the split parts of the
/// stored `Splittable` values independently.
pub fn split<'a, K: 'a, V: 'a, S, SplitType>(v: &'a mut HashMap<K, V, S>) -> (HashMapA<'a, K, V, S, SplitType>, HashMapB<'a, K, V, S, SplitType>)
where K: Eq + Hash, S: BuildHasher, V: Splittable<'a, SplitType> {
    let p = v as * mut _;
    (HashMapA(PhantomData, v), HashMapB(PhantomData, unsafe { &mut*p }))
}

include!(concat!(env!("OUT_DIR"), "/split.rs"));

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use super::*;

    #[derive(Clone, Copy, PartialEq, Debug)]
    struct Pair {
        a: i32,
        b: f32,
    }

    #[derive(Clone, Copy, PartialEq, Debug)]
    struct Quad {
        a: i32,
        b: f32,
        c: u32,
        d: f64,
    }

    impl<'a> Splittable<'a> for Pair {
        type A = i32;
        type B = f32;
        fn split(&self) -> (&Self::A, &Self::B) { (&self.a, &self.b) }
        fn split_mut(&mut self) -> (&mut Self::A, &mut Self::B) { (&mut self.a, &mut self.b) }
    }

    impl<'a> Splittable4<'a> for Quad {
        type A = i32;
        type B = f32;
        type C = u32;
        type D = f64;
        fn split4(&self) -> (&Self::A, &Self::B, &Self::C, &Self::D) {
            (&self.a, &self.b, &self.c, &self.d)
        }
        fn split4_mut(&mut self) -> (&mut Self::A, &mut Self::B, &mut Self::C, &mut Self::D) {
            (&mut self.a, &mut self.b, &mut self.c, &mut self.d)
        }
    }

    #[test]
    fn test_split() {
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

    #[test]
    fn test_split4() {
        let mut h = HashMap::new();
        h.insert(0i32, Quad{a: 1, b: 15.0, c: 1, d: 14.0});
        h.insert(1i32, Quad{a: 3, b: 14.0, c: 3, d: 12.0});
        h.insert(2i32, Quad{a: 0, b: 13.0, c: 0, d: 15.0});
        h.insert(3i32, Quad{a: 2, b: 12.0, c: 2, d: 13.0});

        {
            let (mut a, b) = split(&mut h);
            for (_, v) in a.iter_mut() {
                if let Some(b) = b.get(v) {
                    *v = *b as i32;
                }
            }
        }

        {
            let (_, _, c, mut d) = split4(&mut h);
            for (_, v) in c.iter() {
                let v = *v as i32;
                *d.get_mut(&v).unwrap() += v as f64;
            }
        }

        let mut result = HashMap::new();
        result.insert(0i32, Quad{a: 14, b: 15.0, c: 1, d: 14.0});
        result.insert(1i32, Quad{a: 12, b: 14.0, c: 3, d: 13.0});
        result.insert(2i32, Quad{a: 15, b: 13.0, c: 0, d: 17.0});
        result.insert(3i32, Quad{a: 13, b: 12.0, c: 2, d: 16.0});
        assert_eq!(h, result);

    }
}
