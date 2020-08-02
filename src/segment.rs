// Copyright (C) 2020 Gregory Meyer
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! Segmented lockfree hash tables.
//!
//! Segmented hash tables divide their entries between a number of smaller
//! logical hash tables, or segments. Each segment is entirely independent from
//! the others, and entries are never relocated across segment boundaries.
//!
//! In the context of this crate, a segment refers specifically to an array of
//! bucket pointers. The number of segments in a hash table is rounded up to the
//! nearest power of two; this is so that selecting the segment for a key is no
//! more than a right shift to select the most significant bits of a hashed key.
//!
//! Each segment is entirely independent from the others, all operations can be
//! performed concurrently by multiple threads. Should a set of threads be
//! operating on disjoint sets of segments, the only synchronization between
//! them will be destructive interference as they access and update the bucket
//! array pointer and length for each segment.
//!
//! Compared to the unsegmented hash tables in this crate, the segmented hash
//! tables have higher concurrent write throughput for disjoint sets of keys.
//! However, the segmented hash tables have slightly lower read and
//! single-threaded write throughput. This is because the segmenting structure
//! adds another layer of indirection between the hash table and its buckets.
//!
//! The idea for segmenting hash tables was inspired by the
//! [`ConcurrentHashMap`] from OpenJDK 7, which consists of a number of
//! separately-locked segments. OpenJDK 8 introduced a striped concurrent hash
//! map that stripes a set of bucket locks across the set of buckets using the
//! least significant bits of hashed keys.
//!
//! [`ConcurrentHashMap`]: https://github.com/openjdk-mirror/jdk7u-jdk/blob/master/src/share/classes/java/util/concurrent/ConcurrentHashMap.java

pub mod map;

pub use map::HashMap;
