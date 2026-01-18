struct PairingHeapNode<T> {
    val: T,
    child: Option<Box<PairingHeapNode<T>>>,
    sibling: Option<Box<PairingHeapNode<T>>>,
}

pub struct PairingHeap<T> {
    root: Option<Box<PairingHeapNode<T>>>,
}

impl<T: PartialOrd> PairingHeap<T> {
    pub fn new() -> Self {
        PairingHeap { root: None }
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// O(1)
    pub fn top(&self) -> Option<&T> {
        self.root.as_ref().map(|n| &n.val)
    }

    /// O(1)
    pub fn push(&mut self, val: T) {
        let node = Box::new(PairingHeapNode {
            val,
            child: None,
            sibling: None,
        });
        self.root = Self::link(self.root.take(), Some(node));
    }

    /// O(log n) am.
    pub fn pop(&mut self) -> Option<T> {
        self.root.take().map(|node| {
            self.root = Self::merge_pairs(node.child);
            node.val
        })
    }

    /// O(1)
    pub fn meld(&mut self, other: PairingHeap<T>) {
        self.root = Self::link(self.root.take(), other.root);
    }

    /// O(1)
    fn link(
        a: Option<Box<PairingHeapNode<T>>>,
        b: Option<Box<PairingHeapNode<T>>>,
    ) -> Option<Box<PairingHeapNode<T>>> {
        match (a, b) {
            (None, b) => b,
            (a, None) => a,
            (Some(mut a), Some(mut b)) => {
                if a.val > b.val {
                    std::mem::swap(&mut a, &mut b);
                }
                b.sibling = a.child.take();
                a.child = Some(b);
                Some(a)
            }
        }
    }

    fn merge_pairs(mut head: Option<Box<PairingHeapNode<T>>>) -> Option<Box<PairingHeapNode<T>>> {
        let mut pairs = Vec::new();
        while let Some(mut first) = head {
            head = first.sibling.take();
            if let Some(mut second) = head {
                head = second.sibling.take();
                if first.val > second.val {
                    std::mem::swap(&mut first, &mut second);
                }
                second.sibling = first.child.take();
                first.child = Some(second);
                pairs.push(first);
            } else {
                pairs.push(first);
            }
        }
        pairs
            .into_iter()
            .rev()
            .fold(None, |acc, node| Self::link(acc, Some(node)))
    }
}

impl<T: PartialOrd> Default for PairingHeap<T> {
    fn default() -> Self {
        Self::new()
    }
}
