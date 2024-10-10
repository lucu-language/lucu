use std::{
    fmt,
    num::NonZeroU32,
    ops::{Index, IndexMut},
};

#[derive(Debug, Clone, Copy)]
pub struct Location {
    pub start: u32,
    pub end: u32,
}

impl Location {
    pub const ZERO: Location = Location { start: 0, end: 0 };
}

impl Index<Location> for str {
    type Output = str;

    fn index(&self, index: Location) -> &Self::Output {
        &self[index.start as usize..index.end as usize]
    }
}

#[derive(Debug)]
pub struct NodeData<T> {
    pub variant: Option<T>, // None is the GLUE variant
    pub location: Location,
    pub left: Option<NonZeroU32>,
    pub right: Option<NonZeroU32>,
}

pub struct NodeTree<T> {
    nodes: Vec<NodeData<T>>,
}

impl<T> Default for NodeTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: fmt::Debug> fmt::Debug for NodeTree<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn draw<T: fmt::Debug>(
            me: &NodeTree<T>,
            node: NonZeroU32,
            spaces: u32,
            f: &mut fmt::Formatter<'_>,
        ) -> fmt::Result {
            writeln!(f, "{: <2$}{:?}", "", me[node], spaces as usize)?;
            me.children(node)
                .try_for_each(|n| draw(me, n, spaces + 2, f))?;
            Ok(())
        }
        draw(self, self.root().unwrap(), 0, f)
    }
}

impl<T> NodeTree<T> {
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }
    pub fn push(&mut self, data: NodeData<T>) -> NonZeroU32 {
        self.nodes.push(data);
        unsafe { NonZeroU32::new_unchecked(self.nodes.len() as u32) }
    }
    pub fn get(&self, node: NonZeroU32) -> Option<&NodeData<T>> {
        self.nodes.get(node.get() as usize - 1)
    }
    pub fn get_mut(&mut self, node: NonZeroU32) -> Option<&mut NodeData<T>> {
        self.nodes.get_mut(node.get() as usize - 1)
    }
    pub fn children(&self, node: NonZeroU32) -> impl Iterator<Item = NonZeroU32> + '_ {
        struct Children<'a, T>(&'a NodeTree<T>, Option<NonZeroU32>, bool);
        impl<'a, T> Iterator for Children<'a, T> {
            type Item = NonZeroU32;
            fn next(&mut self) -> Option<Self::Item> {
                let current = self.1?;
                match self.2 {
                    false => {
                        self.2 = true;
                        self.0[current].left
                    }
                    true => {
                        let right = self.0[current].right?;
                        match self.0[right].variant {
                            Some(_) => {
                                self.1 = None;
                                Some(right)
                            }
                            None => {
                                self.1 = Some(right);
                                self.0[right].left
                            }
                        }
                    }
                }
            }
        }
        Children(
            self,
            Some(node),
            self[node].left.is_none() && self[node].right.is_some(),
        )
    }
    pub fn root(&self) -> Option<NonZeroU32> {
        NonZeroU32::new(self.nodes.len() as u32)
    }
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = NonZeroU32> + '_ {
        (1..=self.nodes.len() as u32).filter_map(|idx| {
            let node = unsafe { NonZeroU32::new_unchecked(idx) };

            // remove glue nodes
            self[node].variant.as_ref().map(|_| node)
        })
    }
}

impl<T> Index<NonZeroU32> for NodeTree<T> {
    type Output = NodeData<T>;

    fn index(&self, index: NonZeroU32) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<T> IndexMut<NonZeroU32> for NodeTree<T> {
    fn index_mut(&mut self, index: NonZeroU32) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}
