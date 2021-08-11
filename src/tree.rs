//! General AST
use std::any::Any;
use std::borrow::Borrow;

use std::fmt::{Debug, Formatter};
use std::iter::from_fn;
use std::marker::PhantomData;
use std::ops::{CoerceUnsized, Deref};
use std::rc::Rc;

use crate::atn::INVALID_ALT;
use crate::char_stream::InputData;
use crate::int_stream::EOF;
use crate::interval_set::Interval;
use crate::parser::ParserNodeType;
use crate::parser_rule_context::ParserRuleContext;
use crate::recognizer::Recognizer;
use crate::rule_context::{CustomRuleContext, RuleContext};
use crate::token::Token;
use crate::token_factory::TokenFactory;
use crate::{interval_set, trees};
use better_any::{Tid, TidAble};

//todo try to make in more generic
#[allow(missing_docs)]
pub trait Tree<'input>: NodeText + RuleContext<'input> {
    fn get_parent(&self) -> Option<Rc<<Self::Ctx as ParserNodeType<'input>>::Type>> { None }
    fn has_parent(&self) -> bool { false }
    fn get_payload(&self) -> Box<dyn Any> { unimplemented!() }
    fn get_child(&self, _i: usize) -> Option<Rc<<Self::Ctx as ParserNodeType<'input>>::Type>> {
        None
    }
    fn get_child_count(&self) -> usize { 0 }
    fn get_children<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Rc<<Self::Ctx as ParserNodeType<'input>>::Type>> + 'a>
    where
        'input: 'a,
    {
        let mut index = 0;
        let iter = from_fn(move || {
            if index < self.get_child_count() {
                index += 1;
                self.get_child(index - 1)
            } else {
                None
            }
        });

        Box::new(iter)
    }
    // fn get_children_full(&self) -> &RefCell<Vec<Rc<<Self::Ctx as ParserNodeType<'input, Self::TF>>::Type>>> { unimplemented!() }
}

/// Tree that knows about underlying text
pub trait ParseTree<'input>: Tree<'input> {
    /// Return an {@link Interval} indicating the index in the
    /// {@link TokenStream} of the first and last token associated with this
    /// subtree. If this node is a leaf, then the interval represents a single
    /// token and has interval i..i for token index i.
    fn get_source_interval(&self) -> Interval { interval_set::INVALID }

    /// Return combined text of this AST node.
    /// To create resulting string it does traverse whole subtree,
    /// also it includes only tokens added to the parse tree
    ///
    /// Since tokens on hidden channels (e.g. whitespace or comments) are not
    ///	added to the parse trees, they will not appear in the output of this
    ///	method.
    fn get_text(&self) -> String { String::new() }

    /// Print out a whole tree, not just a node, in LISP format
    /// (root child1 .. childN). Print just a node if this is a leaf.
    /// We have to know the recognizer so we can get rule names.
    fn to_string_tree(
        &self,
        r: &dyn Recognizer<'input, TF = Self::TF, Node = Self::Ctx>,
    ) -> String {
        trees::string_tree(self, r.get_rule_names())
    }
}

/// text of the node.
/// Already implemented for all rule contexts
pub trait NodeText {
    /// Returns text representation of current node type,
    /// rule name for context nodes and token text for terminal nodes
    fn get_node_text(&self, rule_names: &[&str]) -> String;
}

impl<T> NodeText for T {
    default fn get_node_text(&self, _rule_names: &[&str]) -> String { "<unknown>".to_owned() }
}

impl<'input, T: CustomRuleContext<'input>> NodeText for T {
    default fn get_node_text(&self, rule_names: &[&str]) -> String {
        let rule_index = self.get_rule_index();
        let rule_name = rule_names[rule_index];
        let alt_number = self.get_alt_number();
        if alt_number != INVALID_ALT {
            return format!("{}:{}", rule_name, alt_number);
        }
        return rule_name.to_owned();
    }
}

#[doc(hidden)]
#[derive(Tid, Debug)]
pub struct NoError;

#[doc(hidden)]
#[derive(Tid, Debug)]
pub struct IsError;

/// Generic leaf AST node
#[derive(Tid)]
pub struct LeafNode<'input, Node: ParserNodeType<'input>, T: 'static> {
    /// Token, this leaf consist of
    pub symbol: <Node::TF as TokenFactory<'input>>::Tok,
    iserror: PhantomData<T>,
}

impl<'input, Node: ParserNodeType<'input>, T: 'static> CustomRuleContext<'input>
    for LeafNode<'input, Node, T>
{
    type TF = Node::TF;
    type Ctx = Node;

    fn get_rule_index(&self) -> usize { usize::max_value() }
}

impl<'input, Node: ParserNodeType<'input> + TidAble<'input>, T: 'static + TidAble<'input>>
    ParserRuleContext<'input> for LeafNode<'input, Node, T>
{
}

impl<'input, Node: ParserNodeType<'input>, T: 'static> Tree<'input> for LeafNode<'input, Node, T> {}

impl<'input, Node: ParserNodeType<'input>, T: 'static> RuleContext<'input>
    for LeafNode<'input, Node, T>
{
}

impl<'input, Node: ParserNodeType<'input>, T: 'static> NodeText for LeafNode<'input, Node, T> {
    fn get_node_text(&self, _rule_names: &[&str]) -> String {
        self.symbol.borrow().get_text().to_display()
    }
}

impl<'input, Node: ParserNodeType<'input>, T: 'static> ParseTree<'input>
    for LeafNode<'input, Node, T>
{
    fn get_source_interval(&self) -> Interval {
        let i = self.symbol.borrow().get_token_index();
        Interval { a: i, b: i }
    }

    fn get_text(&self) -> String { self.symbol.borrow().get_text().to_display() }
}

impl<'input, Node: ParserNodeType<'input>, T: 'static> Debug for LeafNode<'input, Node, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.symbol.borrow().get_token_type() == EOF {
            f.write_str("<EOF>")
        } else {
            let a = self.symbol.borrow().get_text().to_display();
            f.write_str(&a)
        }
    }
}

impl<'input, Node: ParserNodeType<'input>, T: 'static> LeafNode<'input, Node, T> {
    /// creates new leaf node
    pub fn new(symbol: <Node::TF as TokenFactory<'input>>::Tok) -> Self {
        Self {
            symbol,
            iserror: Default::default(),
        }
    }
}

/// non-error AST leaf node
pub type TerminalNode<'input, NodeType> = LeafNode<'input, NodeType, NoError>;

impl<'input, Node: ParserNodeType<'input>, Listener: ParseTreeListener<'input, Node> + ?Sized>
    Listenable<Listener> for TerminalNode<'input, Node>
{
    fn enter(&self, listener: &mut Listener) { listener.visit_terminal(self) }

    fn exit(&self, _listener: &mut Listener) {
        // do nothing
    }
}

impl<'input, Node: ParserNodeType<'input>, Visitor: ParseTreeVisitor<'input, Node>>
    Visitable<'input, Node, Visitor> for TerminalNode<'input, Node>
where
    <Node as ParserNodeType<'input>>::Type: VisitableDyn<'input, Node, Visitor>,
{
    fn accept(&self, visitor: &mut Visitor) -> Option<Visitor::Ret> { visitor.visit_terminal(self) }
}

/// # Error Leaf
/// Created for each token created or consumed during recovery
pub type ErrorNode<'input, NodeType> = LeafNode<'input, NodeType, IsError>;

impl<'input, Node: ParserNodeType<'input>, Listener: ParseTreeListener<'input, Node> + ?Sized>
    Listenable<Listener> for ErrorNode<'input, Node>
{
    fn enter(&self, listener: &mut Listener) { listener.visit_error_node(self) }

    fn exit(&self, _listener: &mut Listener) {
        // do nothing
    }
}

impl<'input, Node: ParserNodeType<'input>, Visitor: ParseTreeVisitor<'input, Node>>
    Visitable<'input, Node, Visitor> for ErrorNode<'input, Node>
where
    <Node as ParserNodeType<'input>>::Type: VisitableDyn<'input, Node, Visitor>,
{
    fn accept(&self, visitor: &mut Visitor) -> Option<Visitor::Ret> {
        visitor.visit_error_node(self)
    }
}

/// Base interface for visiting over syntax tree
pub trait ParseTreeVisitor<'input, Node: ParserNodeType<'input>>
where
    Node::Type: VisitableDyn<'input, Node, Self>,
{
    /// Return type of visit methods
    type Ret;
    /// Called on terminal(leaf) node
    fn visit_terminal(&mut self, _node: &TerminalNode<'input, Node>) -> Option<Self::Ret> { None }
    /// Called on error node
    fn visit_error_node(&mut self, _node: &ErrorNode<'input, Node>) -> Option<Self::Ret> { None }

    /// Implement this only if you want to change children visiting algorithm
    fn visit_children(&mut self, node: &Node::Type) -> Option<Self::Ret> {
        let mut result: Option<Self::Ret> = None;
        for child in node.get_children() {
            let child_result = (*child).accept_dyn(self);
            result = self.aggregate_result(result, child_result);
        }
        return result;
    }

    /// Algorithm for combining two results from children
    fn aggregate_result(
        &mut self,
        _aggregate: Option<Self::Ret>,
        next_result: Option<Self::Ret>,
    ) -> Option<Self::Ret> {
        return next_result;
    }
}

/// Types that can accept particular visitor
/// ** Usually implemented only in generated parser **
pub trait Visitable<'input, Node: ParserNodeType<'input>, Vis: ParseTreeVisitor<'input, Node>>
where
    <Node as ParserNodeType<'input>>::Type: VisitableDyn<'input, Node, Vis>,
{
    /// Calls corresponding visit callback on visitor`Vis`
    fn accept(&self, _visitor: &mut Vis) -> Option<Vis::Ret> {
        unreachable!("should have been properly implemented by generated context when reachable")
    }
}

// workaround trait for accepting sized visitor on rule context trait object
#[doc(hidden)]
pub trait VisitableDyn<
    'input,
    Node: ParserNodeType<'input>,
    Vis: ParseTreeVisitor<'input, Node> + ?Sized,
> where
    <Node as ParserNodeType<'input>>::Type: VisitableDyn<'input, Node, Vis>,
{
    fn accept_dyn(&self, _visitor: &mut Vis) -> Option<Vis::Ret> {
        unreachable!("should have been properly implemented by generated context when reachable")
    }
}

/// Base parse listener interface
pub trait ParseTreeListener<'input, Node: ParserNodeType<'input>> {
    /// Called when parser creates terminal node
    fn visit_terminal(&mut self, _node: &TerminalNode<'input, Node>) {}
    /// Called when parser creates error node
    fn visit_error_node(&mut self, _node: &ErrorNode<'input, Node>) {}
    /// Called when parser enters any rule node
    fn enter_every_rule(&mut self, _ctx: &Node::Type) {}
    /// Called when parser exits any rule node
    fn exit_every_rule(&mut self, _ctx: &Node::Type) {}
}

/// Types that can accept particular listener
/// ** Usually implemented only in generated parser **
pub trait Listenable<T: ?Sized> {
    /// Calls corresponding enter callback on listener `T`
    fn enter(&self, _listener: &mut T) {}
    /// Calls corresponding exit callback on listener `T`
    fn exit(&self, _listener: &mut T) {}
}

// #[inline]
// pub fn temp_to_trait<Z,TraitObject>(mut input: Z, f:impl FnOnce(&mut TraitObject)) -> Z where &mut Z:CoerceUnsized<&mut TraitObject>{
//     let a = &mut input as &mut TraitObject;
//     f(a)
// }

/// Helper struct to accept parse listener on already generated tree
#[derive(Debug)]
pub struct ParseTreeWalker<'input, 'a, Node, T = dyn ParseTreeListener<'input, Node> + 'a>(
    PhantomData<fn(&'a T) -> &'input Node::Type>,
)
where
    Node: ParserNodeType<'input>,
    T: ParseTreeListener<'input, Node> + ?Sized;

impl<'input, 'a, Node, T> ParseTreeWalker<'input, 'a, Node, T>
where
    Node: ParserNodeType<'input>,
    T: ParseTreeListener<'input, Node> + 'a + ?Sized,
    Node::Type: Listenable<T>,
{
    /// Walks recursively over tree `t` with `listener`
    pub fn walk<Listener, Ctx>(mut listener: Box<Listener>, t: &Ctx) -> Box<Listener>
    where
        for<'x> &'x mut Listener: CoerceUnsized<&'x mut T>,
        for<'x> &'x Ctx: CoerceUnsized<&'x Node::Type>,
    {
        // let mut listener = listener as Box<T>;
        Self::walk_inner(listener.as_mut(), t as &Node::Type);

        // just cast back
        // unsafe { Box::<Listener>::from_raw(Box::into_raw(listener) as *mut _) }
        listener
    }

    fn walk_inner(listener: &mut T, t: &Node::Type) {
        t.enter(listener);

        for child in t.get_children() {
            Self::walk_inner(listener, child.deref())
        }

        t.exit(listener);
    }
}
