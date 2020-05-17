// Generated from SimpleLR.g4 by ANTLR 4.8
#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(nonstandard_style)]
#![allow(unused_imports)]
#![allow(unused_mut)]

use std::any::{Any, TypeId};
use std::borrow::{Borrow, BorrowMut};
use std::cell::RefCell;
use std::convert::TryFrom;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;
use std::sync::Arc;

use antlr_rust::atn::{ATN, INVALID_ALT};
use antlr_rust::atn_deserializer::ATNDeserializer;
use antlr_rust::dfa::DFA;
use antlr_rust::error_strategy::{DefaultErrorStrategy, ErrorStrategy};
use antlr_rust::errors::*;
use antlr_rust::int_stream::EOF;
use antlr_rust::parser::{BaseParser, Listenable, Parser, ParserNodeType, ParserRecog};
use antlr_rust::parser_atn_simulator::ParserATNSimulator;
use antlr_rust::parser_rule_context::{BaseParserRuleContext, cast, cast_mut, ParserRuleContext};
use antlr_rust::PredictionContextCache;
use antlr_rust::recognizer::{Actions, Recognizer};
use antlr_rust::rule_context::{BaseRuleContext, CustomRuleContext, RuleContext};
use antlr_rust::token::{OwningToken, Token, TOKEN_EOF};
use antlr_rust::token_factory::{CommonTokenFactory, TokenAware, TokenFactory};
use antlr_rust::token_source::TokenSource;
use antlr_rust::token_stream::TokenStream;
use antlr_rust::tree::{ErrorNode, LeafNode, ParseTree, ParseTreeListener, ParseTreeWalker, TerminalNode};
use antlr_rust::vocabulary::{Vocabulary, VocabularyImpl};

use super::simplelrlistener::*;

pub const ID: isize = 1;
pub const WS: isize = 2;
pub const RULE_s: usize = 0;
pub const RULE_a: usize = 1;
pub const ruleNames: [&'static str; 2] = [
    "s", "a"
];


pub const _LITERAL_NAMES: [Option<&'static str>; 0] = [];
pub const _SYMBOLIC_NAMES: [Option<&'static str>; 3] = [
    None, Some("ID"), Some("WS")
];
lazy_static! {
	    static ref _shared_context_cache: Arc<PredictionContextCache> = Arc::new(PredictionContextCache::new());
		static ref VOCABULARY: Box<dyn Vocabulary> = Box::new(VocabularyImpl::new(_LITERAL_NAMES.iter(), _SYMBOLIC_NAMES.iter(), None));
	}


type BaseParserType<'input, I> =
BaseParser<'input, SimpleLRParserExt, I, SimpleLRParserContextType, dyn SimpleLRListener<'input> + 'static>;

type TokenType<'input> = <LocalTokenFactory<'input> as TokenFactory<'input>>::Tok;
pub type LocalTokenFactory<'input> = CommonTokenFactory;

pub type SimpleLRTreeWalker<'input, 'a> =
ParseTreeWalker<'input, 'a, SimpleLRParserContextType, dyn SimpleLRListener<'input> + 'a>;

pub struct SimpleLRParser<'input, I: TokenStream<'input, TF=LocalTokenFactory<'input>>> {
    base: BaseParserType<'input, I>,
    interpreter: Arc<ParserATNSimulator>,
    _shared_context_cache: Box<PredictionContextCache>,
    pub err_handler: Box<dyn ErrorStrategy<'input, BaseParserType<'input, I>> + 'input>,
}

impl<'input, I: TokenStream<'input, TF=LocalTokenFactory<'input>>> SimpleLRParser<'input, I> {
    pub fn get_serialized_atn() -> &'static str { unimplemented!() }

    pub fn set_error_strategy(&mut self, strategy: Box<dyn ErrorStrategy<'input, BaseParserType<'input, I>>>) {
        self.err_handler = strategy
    }

    pub fn new(input: Box<I>) -> Self {
        antlr_rust::recognizer::check_version("0", "2");
        let interpreter = Arc::new(ParserATNSimulator::new(
            _ATN.clone(),
            _decision_to_DFA.clone(),
            _shared_context_cache.clone(),
        ));
        Self {
            base: BaseParser::new_base_parser(
                input,
                Arc::clone(&interpreter),
                SimpleLRParserExt {},
            ),
            interpreter,
            _shared_context_cache: Box::new(PredictionContextCache::new()),
            err_handler: Box::new(DefaultErrorStrategy::<'input, SimpleLRParserContextType>::new()),
        }
    }
}

/// Trait for monomorphized trait object that corresponds to nodes of parse tree generated by SimpleLRParser
pub trait SimpleLRParserContext<'input>:
    for<'x> Listenable<'input, dyn SimpleLRListener<'input> + 'x>
+ ParserRuleContext<'input, TF=LocalTokenFactory<'input>, Ctx=SimpleLRParserContextType>
{}

impl<'input> SimpleLRParserContext<'input> for TerminalNode<'input, SimpleLRParserContextType> {}

impl<'input> SimpleLRParserContext<'input> for ErrorNode<'input, SimpleLRParserContextType> {}

pub struct SimpleLRParserContextType;

impl<'input> ParserNodeType<'input> for SimpleLRParserContextType {
    type TF = LocalTokenFactory<'input>;
    type Type = dyn SimpleLRParserContext<'input> + 'input;
}

impl<'input, I: TokenStream<'input, TF=LocalTokenFactory<'input>>> Deref for SimpleLRParser<'input, I> {
    type Target = BaseParserType<'input, I>;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

impl<'input, I: TokenStream<'input, TF=LocalTokenFactory<'input>>> DerefMut for SimpleLRParser<'input, I> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.base
    }
}

pub struct SimpleLRParserExt {}

impl SimpleLRParserExt {}


impl<'input> TokenAware<'input> for SimpleLRParserExt {
    type TF = LocalTokenFactory<'input>;
}

impl<'input, I: TokenStream<'input, TF=LocalTokenFactory<'input>>> ParserRecog<'input, BaseParserType<'input, I>> for SimpleLRParserExt {}

impl<'input, I: TokenStream<'input, TF=LocalTokenFactory<'input>>> Actions<'input, BaseParserType<'input, I>> for SimpleLRParserExt {
    fn get_grammar_file_name(&self) -> &str { "SimpleLR.g4" }

    fn get_rule_names(&self) -> &[&str] { &ruleNames }

    fn get_vocabulary(&self) -> &dyn Vocabulary { &**VOCABULARY }
    fn sempred(_localctx: &(dyn SimpleLRParserContext<'input> + 'input), rule_index: isize, pred_index: isize,
               recog: &mut BaseParserType<'input, I>,
    ) -> bool {
        match rule_index {
            1 => SimpleLRParser::<'input, I>::a_sempred(cast::<_, AContext<'input>>(_localctx), pred_index, recog),
            _ => true
        }
    }
}

impl<'input, I: TokenStream<'input, TF=LocalTokenFactory<'input>>> SimpleLRParser<'input, I> {
    fn a_sempred(_localctx: &AContext<'input>, pred_index: isize,
                 recog: &mut <Self as Deref>::Target,
    ) -> bool {
        match pred_index {
            0 => {
                recog.precpred(None, 2)
            }
            _ => true
        }
    }
}
//------------------- s ----------------
pub type SContextAll<'input> = SContext<'input>;


pub type SContext<'input> = BaseParserRuleContext<'input, SContextExt<'input>>;

#[derive(Clone)]
pub struct SContextExt<'input> {
    ph: PhantomData<&'input str>
}

impl<'input> SimpleLRParserContext<'input> for SContext<'input> {}

impl<'input, 'a> Listenable<'input, dyn SimpleLRListener<'input> + 'a> for SContext<'input> {
    fn enter(&self, listener: &mut (dyn SimpleLRListener<'input> + 'a)) {
        listener.enter_every_rule(self);
        listener.enter_s(self);
    }
    fn exit(&self, listener: &mut (dyn SimpleLRListener<'input> + 'a)) {
        listener.exit_s(self);
        listener.exit_every_rule(self);
    }
}

impl<'input> CustomRuleContext<'input> for SContextExt<'input> {
    type TF = LocalTokenFactory<'input>;
    type Ctx = SimpleLRParserContextType;
    fn get_rule_index(&self) -> usize { RULE_s }
    //fn type_rule_index() -> usize where Self: Sized { RULE_s }
}
antlr_rust::type_id! {SContextExt}

impl<'input> SContextExt<'input> {
    fn new(parent: Option<Rc<dyn SimpleLRParserContext<'input> + 'input>>, invoking_state: isize) -> Rc<SContextAll<'input>> {
        Rc::new(
            BaseParserRuleContext::new_parser_ctx(parent, invoking_state, SContextExt {
                ph: PhantomData
            }),
        )
    }
}

pub trait SContextAttrs<'input>: SimpleLRParserContext<'input> + BorrowMut<SContextExt<'input>> {
    fn a(&self) -> Option<Rc<AContextAll<'input>>> where Self: Sized {
        self.child_of_type(0)
    }
}

impl<'input> SContextAttrs<'input> for SContext<'input> {}

impl<'input, I: TokenStream<'input, TF=LocalTokenFactory<'input>>> SimpleLRParser<'input, I> {
    pub fn s(&mut self)
             -> Result<Rc<SContextAll<'input>>, ANTLRError> {
        let mut recog = self;
        let _parentctx = recog.ctx.take();
        let mut _localctx = SContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 0, RULE_s);
        let mut _localctx: Rc<SContextAll> = _localctx;
        let result: Result<(), ANTLRError> = try {

            //recog.base.enter_outer_alt(_localctx.clone(), 1);
            recog.base.enter_outer_alt(None, 1);
            {
                /*InvokeRule a*/
                recog.base.set_state(4);
                recog.a_rec(0)?;
            }
			let tmp = recog.input.lt(-1).cloned();
			recog.ctx.as_ref().unwrap().set_stop(tmp);
			println!("test");
		};
		match result {
            Ok(_) => {},
            Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
            Err(ref re) => {
                //_localctx.exception = re;
                recog.err_handler.report_error(&mut recog.base, re);
                recog.err_handler.recover(&mut recog.base, re)?;
            }
        }
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- a ----------------
pub type AContextAll<'input> = AContext<'input>;


pub type AContext<'input> = BaseParserRuleContext<'input, AContextExt<'input>>;

#[derive(Clone)]
pub struct AContextExt<'input> {
    ph: PhantomData<&'input str>
}

impl<'input> SimpleLRParserContext<'input> for AContext<'input> {}

impl<'input, 'a> Listenable<'input, dyn SimpleLRListener<'input> + 'a> for AContext<'input> {
    fn enter(&self, listener: &mut (dyn SimpleLRListener<'input> + 'a)) {
        listener.enter_every_rule(self);
        listener.enter_a(self);
    }
    fn exit(&self, listener: &mut (dyn SimpleLRListener<'input> + 'a)) {
        listener.exit_a(self);
        listener.exit_every_rule(self);
    }
}

impl<'input> CustomRuleContext<'input> for AContextExt<'input> {
    type TF = LocalTokenFactory<'input>;
    type Ctx = SimpleLRParserContextType;
    fn get_rule_index(&self) -> usize { RULE_a }
    //fn type_rule_index() -> usize where Self: Sized { RULE_a }
}
antlr_rust::type_id! {AContextExt}

impl<'input> AContextExt<'input> {
    fn new(parent: Option<Rc<dyn SimpleLRParserContext<'input> + 'input>>, invoking_state: isize) -> Rc<AContextAll<'input>> {
        Rc::new(
            BaseParserRuleContext::new_parser_ctx(parent, invoking_state, AContextExt {
                ph: PhantomData
            }),
        )
    }
}

pub trait AContextAttrs<'input>: SimpleLRParserContext<'input> + BorrowMut<AContextExt<'input>> {
    /// Retrieves first TerminalNode corresponding to token ID
    /// Returns `None` if there is no child corresponding to token ID
    fn ID(&self) -> Option<Rc<TerminalNode<'input, SimpleLRParserContextType>>> where Self: Sized {
        self.get_token(ID, 0)
    }
    fn a(&self) -> Option<Rc<AContextAll<'input>>> where Self: Sized {
        self.child_of_type(0)
    }
}

impl<'input> AContextAttrs<'input> for AContext<'input> {}

impl<'input, I: TokenStream<'input, TF=LocalTokenFactory<'input>>> SimpleLRParser<'input, I> {
    pub fn a(&mut self)
             -> Result<Rc<AContextAll<'input>>, ANTLRError> {
        self.a_rec(0)
    }

    fn a_rec(&mut self, _p: isize)
             -> Result<Rc<AContextAll<'input>>, ANTLRError> {
        let recog = self;
        let _parentctx = recog.ctx.take();
        let _parentState = recog.base.get_state();
        let mut _localctx = AContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_recursion_rule(_localctx.clone(), 2, RULE_a, _p);
        let mut _localctx: Rc<AContextAll> = _localctx;
        let mut _prevctx = _localctx.clone();
        let _startState = 2;
        let result: Result<(), ANTLRError> = try {
            let mut _alt: isize;
            //recog.base.enter_outer_alt(_localctx.clone(), 1);
            recog.base.enter_outer_alt(None, 1);
            {
                {
                    recog.base.set_state(7);
                    recog.base.match_token(ID, recog.err_handler.as_mut())?;
                }
                let tmp = recog.input.lt(-1).cloned();
                recog.ctx.as_ref().unwrap().set_stop(tmp);
                recog.base.set_state(13);
                recog.err_handler.sync(&mut recog.base)?;
                _alt = recog.interpreter.adaptive_predict(0, &mut recog.base)?;
                while { _alt != 2 && _alt != INVALID_ALT } {
                    if _alt == 1 {
                        recog.trigger_exit_rule_event();
                        _prevctx = _localctx.clone();
                        {
                            {
                                /*recRuleAltStartAction*/
                                let mut tmp = AContextExt::new(_parentctx.clone(), _parentState);
                                recog.push_new_recursion_context(tmp.clone(), _startState, RULE_a);
                                _localctx = tmp;
                                recog.base.set_state(9);
                                if !({ recog.precpred(None, 2) }) {
                                    Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 2)".to_owned()), None))?;
                                }
                                recog.base.set_state(10);
                                recog.base.match_token(ID, recog.err_handler.as_mut())?;
                            }
                        }
                    }
                    recog.base.set_state(15);
                    recog.err_handler.sync(&mut recog.base)?;
                    _alt = recog.interpreter.adaptive_predict(0, &mut recog.base)?;
                }
            }
		};
		match result {
            Ok(_) => {},
            Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
            Err(ref re) => {
                //_localctx.exception = re;
                recog.err_handler.report_error(&mut recog.base, re);
                recog.err_handler.recover(&mut recog.base, re)?;
            }
        }
		recog.base.unroll_recursion_context(_parentctx);

		Ok(_localctx)
	}
}

lazy_static! {
    static ref _ATN: Arc<ATN> =
        Arc::new(ATNDeserializer::new(None).deserialize(_serializedATN.chars()));
    static ref _decision_to_DFA: Arc<Vec<DFA>> = {
        let mut dfa = Vec::new();
        let size = _ATN.decision_to_state.len();
        for i in 0..size {
            dfa.push(DFA::new(
                _ATN.clone(),
                _ATN.get_decision_state(i),
                i as isize,
            ))
        }
        Arc::new(dfa)
    };
}



const _serializedATN: &'static str =
    "\x03\u{608b}\u{a72a}\u{8133}\u{b9ed}\u{417c}\u{3be7}\u{7786}\u{5964}\x03\
	\x04\x13\x04\x02\x09\x02\x04\x03\x09\x03\x03\x02\x03\x02\x03\x03\x03\x03\
	\x03\x03\x03\x03\x03\x03\x07\x03\x0e\x0a\x03\x0c\x03\x0e\x03\x11\x0b\x03\
	\x03\x03\x02\x03\x04\x04\x02\x04\x02\x02\x02\x11\x02\x06\x03\x02\x02\x02\
	\x04\x08\x03\x02\x02\x02\x06\x07\x05\x04\x03\x02\x07\x03\x03\x02\x02\x02\
	\x08\x09\x08\x03\x01\x02\x09\x0a\x07\x03\x02\x02\x0a\x0f\x03\x02\x02\x02\
	\x0b\x0c\x0c\x04\x02\x02\x0c\x0e\x07\x03\x02\x02\x0d\x0b\x03\x02\x02\x02\
	\x0e\x11\x03\x02\x02\x02\x0f\x0d\x03\x02\x02\x02\x0f\x10\x03\x02\x02\x02\
	\x10\x05\x03\x02\x02\x02\x11\x0f\x03\x02\x02\x02\x03\x0f";


