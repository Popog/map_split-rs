use std::env;
use std::fs::File;
use std::io::{Write,Result};
use std::path::Path;

const MAX_TYPES: u8 = 26;


pub fn build_trait(out_dir: &String) -> Result<()> {
    let dest_path = Path::new(out_dir).join("splittable.rs");
    let mut f = File::create(&dest_path).unwrap();

    let mut nm1: String = "".to_string();
    for i in 3..(MAX_TYPES+1) {
        try!(write!(f, "
/// A type which can be split into disjoint references. SplitType allows a type to be split multiple
// ways.
pub trait Splittable{n}<'a, SplitType = ()> {{\n", n=i));
        for j in 0..i {
            try!(write!(f, "\ttype {A}: 'a;\n", A=('A' as u8 + j) as char));
        }
        try!(write!(f, "
    fn split{n}(&'a self) -> (", n=i));
        for j in 0..i {
            try!(write!(f, "&'a Self::{A}, ", A=('A' as u8 + j) as char));
        }
        try!(write!(f, ");
    fn split{n}_mut(&'a mut self) -> (", n=i));
        for j in 0..i {
            try!(write!(f, "&'a mut Self::{A}, ", A=('A' as u8 + j) as char));
        }
        try!(write!(f, ");\n}}\n"));

        try!(write!(f, "impl <'a, SplitType, T: Splittable{n}<'a, SplitType>> Splittable{nm1}<'a, SplitType> for T {{\n", nm1=nm1, n=i));
        for j in 0..i-1 {
            try!(write!(f, "\ttype {A} = <Self as Splittable{n}<'a, SplitType>>::{A};\n", A=('A' as u8 + j) as char, n=i));
        }
        try!(write!(f, "\n\tfn split{nm1}(&'a self) -> (", nm1=nm1));
        for j in 0..i-1 {
            try!(write!(f, "&'a Self::{A}, ", A=('A' as u8 + j) as char));
        }
        try!(write!(f, ") {{
        let r = self.split{n}();
        (", n=i));
        for j in 0..i-1 {
            try!(write!(f, "r.{j}, ", j=j));
        }
            try!(write!(f, ")
    }}
    fn split{nm1}_mut(&'a mut self) -> (", nm1=nm1));
        for j in 0..i-1 {
            try!(write!(f, "&'a mut Self::{A}, ", A=('A' as u8 + j) as char));
        }
        try!(write!(f, ") {{
        let r = self.split{n}_mut();
        (", n=i));
        for j in 0..i-1 {
            try!(write!(f, "r.{j}, ", j=j));
        }
        try!(write!(f, ")\n\t}}\n}}\n"));
        nm1 = i.to_string();
    }

    write!(f, "\n")
}

pub fn build_helpers(out_dir: &String) -> Result<()> {
    let dest_path = Path::new(out_dir).join("helpers.rs");
    let mut f = File::create(&dest_path).unwrap();

    for i in 3..(MAX_TYPES+1) {
        try!(write!(f, "
fn iter_{a}_helper<'a, K: 'a, V: 'a, SplitType>((k, v): (&'a K, &'a V)) ->
    (&'a K, &'a <V as Splittable{n}<'a, SplitType>>::{A})
where V: Splittable{n}<'a, SplitType> {{
    (k, v.split{n}().{nm1})
}}

fn iter_mut_{a}_helper<'a, K: 'a, V: 'a, SplitType>((k, v): (&'a K, &'a mut V)) -> (&'a K, &'a mut <V as Splittable{n}<'a, SplitType>>::{A})
where V: Splittable{n}<'a, SplitType> {{
    (k, v.split{n}_mut().{nm1})
}}
\n", n=i, nm1=i-1, A=('A' as u8 + i - 1) as char, a=('a' as u8 + i - 1) as char));

    }

    write!(f, "\n")
}

pub fn build_structs(out_dir: &String) -> Result<()> {
    let dest_path = Path::new(out_dir).join("structs.rs");
    let mut f = File::create(&dest_path).unwrap();

    for i in 3..(MAX_TYPES+1) {
        try!(write!(f, "
/// A wrapper around a HashMap which provides access to the {A} portion of a `Splittable{n}` value type
pub struct HashMap{A}<'a, K: 'a, V: 'a, S: 'a, SplitType>(PhantomData<SplitType>, &'a mut HashMap<K, V, S>)
where K: Eq + Hash, S: BuildHasher;
\n", n=i, A=('A' as u8 + i - 1) as char));
    }

    write!(f, "\n")
}

pub fn build_impls(out_dir: &String) -> Result<()> {
    let dest_path = Path::new(out_dir).join("impls.rs");
    let mut f = File::create(&dest_path).unwrap();

    for i in 3..(MAX_TYPES+1) {
        try!(write!(f, "
impl <'a, K: 'a, V: 'a, S, SplitType> HashMap{A}<'a, K, V, S, SplitType>
where K: Eq + Hash, S: BuildHasher {{
    /// An iterator visiting all key-value pairs in arbitrary order. Iterator element type is
    /// `(&'b K, &'b V::{A})`.
    pub fn iter<'b>(&'b self) -> iter::Map<
        Iter<'b, K, V>,
        fn((&'b K, &'b V)) -> (&'b K, &'b <V as Splittable{n}<'b, SplitType>>::{A}),
    >
    where V: Splittable{n}<'b, SplitType> {{
        self.1.iter().map(iter_{a}_helper::<'b, K, V, SplitType>)
    }}

    /// An iterator visiting all key-value pairs in arbitrary order. Iterator element type is
    /// `(&'b K, &'b mut V::{A})`.
    pub fn iter_mut<'b>(&'b mut self) -> iter::Map<
        IterMut<'b, K, V>,
        fn((&'b K, &'b mut V)) -> (&'b K, &'b mut <V as Splittable{n}<'b, SplitType>>::{A}),
    >
    where V: Splittable{n}<'b, SplitType> {{
        self.1.iter_mut().map(iter_mut_{a}_helper::<'b, K, V, SplitType>)
    }}

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the HashMap<K, V> might be able to hold more, but is
    /// guaranteed to be able to hold at least this many.
    pub fn capacity(&self) -> usize {{ self.1.capacity() }}

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {{ self.1.len() }}

    /// Returns true if the map contains no elements.
    pub fn is_empty(&self) -> bool {{ self.1.is_empty() }}

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form must match those for the key type.
    pub fn get<'b, Q: ?Sized>(&'b self, k: &Q) -> Option<&'b <V as Splittable{n}<'b, SplitType>>::{A}>
    where Q: Hash + Eq, K: Borrow<Q>, V: Splittable{n}<'b, SplitType> {{
        self.1.get(k).map(|v| v.split{n}().{nm1})
    }}

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form must match those for the key type.
    pub fn get_mut<'b, Q: ?Sized>(&'b mut self, k: &Q) -> Option<&'b mut <V as Splittable{n}<'b, SplitType>>::{A}>
    where Q: Hash + Eq, K: Borrow<Q>, V: Splittable{n}<'b, SplitType> {{
        self.1.get_mut(k).map(|v| v.split{n}_mut().{nm1})
    }}
}}
\n", n=i, nm1=i-1, A=('A' as u8 + i - 1) as char, a=('a' as u8 + i - 1) as char));
    }

    write!(f, "\n")
}

pub fn build_split(out_dir: &String) -> Result<()> {
    let dest_path = Path::new(out_dir).join("split.rs");
    let mut f = File::create(&dest_path).unwrap();

    for i in 3..(MAX_TYPES+1) {
        try!(write!(f, "
/// Splits a `HashMap` into {n} disjoint hashmap references, able to access the split parts of the
/// stored `Splittable{n}` values independently.
pub fn split{n}<'a, K: 'a, V: 'a, S, SplitType>(v: &'a mut HashMap<K, V, S>) -> (", n=i));

        for j in 0..i {
            try!(write!(f, "HashMap{A}<'a, K, V, S, SplitType>, ", A=('A' as u8 + j) as char));
        }
        try!(write!(f, ")
where K: Eq + Hash, S: BuildHasher, V: Splittable{n}<'a, SplitType> {{
    let p = v as * mut _;
    (HashMapA(PhantomData, v)", n=i));

        for j in 1..i {
            try!(write!(f, ", HashMap{A}(PhantomData, unsafe {{ &mut*p }})", A=('A' as u8 + j) as char));
        }
        try!(write!(f, ")\n}}\n"));
    }

    write!(f, "\n")
}

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    build_trait(&out_dir).unwrap();
    build_helpers(&out_dir).unwrap();
    build_structs(&out_dir).unwrap();
    build_impls(&out_dir).unwrap();
    build_split(&out_dir).unwrap();
}
