// MIT License
//
// Copyright (c) 2019 Gregory Meyer
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation files
// (the "Software"), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of the Software,
// and to permit persons to whom the Software is furnished to do so,
// subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

pub mod map;
pub mod set;

pub use map::HashMap;
pub use set::HashSet;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_map_basics() {
        let map = HashMap::with_capacity(64);

        assert_eq!(map.insert("foo".to_string(), 5), None);
        assert_eq!(map.insert("bar".to_string(), 10), None);
        assert_eq!(map.insert("baz".to_string(), 15), None);
        assert_eq!(map.insert("qux".to_string(), 20), None);

        assert_eq!(map.get("foo"), Some(5));
        assert_eq!(map.get("bar"), Some(10));
        assert_eq!(map.get("baz"), Some(15));
        assert_eq!(map.get("qux"), Some(20));

        assert_eq!(
            map.insert("qux".to_string(), 5),
            Some(("qux".to_string(), 20))
        );
        assert_eq!(
            map.insert("baz".to_string(), 10),
            Some(("baz".to_string(), 15))
        );
        assert_eq!(
            map.insert("bar".to_string(), 15),
            Some(("bar".to_string(), 10))
        );
        assert_eq!(
            map.insert("foo".to_string(), 20),
            Some(("foo".to_string(), 5))
        );
    }
}
