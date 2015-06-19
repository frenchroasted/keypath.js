/* */ 
var Token = require("../Token").Token;
var Interval = require("../IntervalSet").Interval;
var IntervalSet = require("../IntervalSet").IntervalSet;
var Predicate = require("./SemanticContext").Predicate;
var PrecedencePredicate = require("./SemanticContext").PrecedencePredicate;
function Transition(target) {
  if (target === undefined || target === null) {
    throw "target cannot be null.";
  }
  this.target = target;
  this.isEpsilon = false;
  this.label = null;
  return this;
}
Transition.EPSILON = 1;
Transition.RANGE = 2;
Transition.RULE = 3;
Transition.PREDICATE = 4;
Transition.ATOM = 5;
Transition.ACTION = 6;
Transition.SET = 7;
Transition.NOT_SET = 8;
Transition.WILDCARD = 9;
Transition.PRECEDENCE = 10;
Transition.serializationNames = ["INVALID", "EPSILON", "RANGE", "RULE", "PREDICATE", "ATOM", "ACTION", "SET", "NOT_SET", "WILDCARD", "PRECEDENCE"];
Transition.serializationTypes = {
  EpsilonTransition: Transition.EPSILON,
  RangeTransition: Transition.RANGE,
  RuleTransition: Transition.RULE,
  PredicateTransition: Transition.PREDICATE,
  AtomTransition: Transition.ATOM,
  ActionTransition: Transition.ACTION,
  SetTransition: Transition.SET,
  NotSetTransition: Transition.NOT_SET,
  WildcardTransition: Transition.WILDCARD,
  PrecedencePredicateTransition: Transition.PRECEDENCE
};
function AtomTransition(target, label) {
  Transition.call(this, target);
  this.label_ = label;
  this.label = this.makeLabel();
  this.serializationType = Transition.ATOM;
  return this;
}
AtomTransition.prototype = Object.create(Transition.prototype);
AtomTransition.prototype.constructor = AtomTransition;
AtomTransition.prototype.makeLabel = function() {
  var s = new IntervalSet();
  s.addOne(this.label_);
  return s;
};
AtomTransition.prototype.matches = function(symbol, minVocabSymbol, maxVocabSymbol) {
  return this.label_ === symbol;
};
AtomTransition.prototype.toString = function() {
  return this.label_;
};
function RuleTransition(ruleStart, ruleIndex, precedence, followState) {
  Transition.call(this, ruleStart);
  this.ruleIndex = ruleIndex;
  this.precedence = precedence;
  this.followState = followState;
  this.serializationType = Transition.RULE;
  this.isEpsilon = true;
  return this;
}
RuleTransition.prototype = Object.create(Transition.prototype);
RuleTransition.prototype.constructor = RuleTransition;
RuleTransition.prototype.matches = function(symbol, minVocabSymbol, maxVocabSymbol) {
  return false;
};
function EpsilonTransition(target, outermostPrecedenceReturn) {
  Transition.call(this, target);
  this.serializationType = Transition.EPSILON;
  this.isEpsilon = true;
  this.outermostPrecedenceReturn = outermostPrecedenceReturn;
  return this;
}
EpsilonTransition.prototype = Object.create(Transition.prototype);
EpsilonTransition.prototype.constructor = EpsilonTransition;
EpsilonTransition.prototype.matches = function(symbol, minVocabSymbol, maxVocabSymbol) {
  return false;
};
EpsilonTransition.prototype.toString = function() {
  return "epsilon";
};
function RangeTransition(target, start, stop) {
  Transition.call(this, target);
  this.serializationType = Transition.RANGE;
  this.start = start;
  this.stop = stop;
  this.label = this.makeLabel();
  return this;
}
RangeTransition.prototype = Object.create(Transition.prototype);
RangeTransition.prototype.constructor = RangeTransition;
RangeTransition.prototype.makeLabel = function() {
  var s = new IntervalSet();
  s.addRange(this.start, this.stop);
  return s;
};
RangeTransition.prototype.matches = function(symbol, minVocabSymbol, maxVocabSymbol) {
  return symbol >= this.start && symbol <= this.stop;
};
RangeTransition.prototype.toString = function() {
  return "'" + String.fromCharCode(this.start) + "'..'" + String.fromCharCode(this.stop) + "'";
};
function AbstractPredicateTransition(target) {
  Transition.call(this, target);
  return this;
}
AbstractPredicateTransition.prototype = Object.create(Transition.prototype);
AbstractPredicateTransition.prototype.constructor = AbstractPredicateTransition;
function PredicateTransition(target, ruleIndex, predIndex, isCtxDependent) {
  AbstractPredicateTransition.call(this, target);
  this.serializationType = Transition.PREDICATE;
  this.ruleIndex = ruleIndex;
  this.predIndex = predIndex;
  this.isCtxDependent = isCtxDependent;
  this.isEpsilon = true;
  return this;
}
PredicateTransition.prototype = Object.create(AbstractPredicateTransition.prototype);
PredicateTransition.prototype.constructor = PredicateTransition;
PredicateTransition.prototype.matches = function(symbol, minVocabSymbol, maxVocabSymbol) {
  return false;
};
PredicateTransition.prototype.getPredicate = function() {
  return new Predicate(this.ruleIndex, this.predIndex, this.isCtxDependent);
};
PredicateTransition.prototype.toString = function() {
  return "pred_" + this.ruleIndex + ":" + this.predIndex;
};
function ActionTransition(target, ruleIndex, actionIndex, isCtxDependent) {
  Transition.call(this, target);
  this.serializationType = Transition.ACTION;
  this.ruleIndex = ruleIndex;
  this.actionIndex = actionIndex === undefined ? -1 : actionIndex;
  this.isCtxDependent = isCtxDependent === undefined ? false : isCtxDependent;
  this.isEpsilon = true;
  return this;
}
ActionTransition.prototype = Object.create(Transition.prototype);
ActionTransition.prototype.constructor = ActionTransition;
ActionTransition.prototype.matches = function(symbol, minVocabSymbol, maxVocabSymbol) {
  return false;
};
ActionTransition.prototype.toString = function() {
  return "action_" + this.ruleIndex + ":" + this.actionIndex;
};
function SetTransition(target, set) {
  Transition.call(this, target);
  this.serializationType = Transition.SET;
  if (set !== undefined && set !== null) {
    this.label = set;
  } else {
    this.label = new IntervalSet();
    this.label.addOne(Token.INVALID_TYPE);
  }
  return this;
}
SetTransition.prototype = Object.create(Transition.prototype);
SetTransition.prototype.constructor = SetTransition;
SetTransition.prototype.matches = function(symbol, minVocabSymbol, maxVocabSymbol) {
  return this.label.contains(symbol);
};
SetTransition.prototype.toString = function() {
  return this.label.toString();
};
function NotSetTransition(target, set) {
  SetTransition.call(this, target, set);
  this.serializationType = Transition.NOT_SET;
  return this;
}
NotSetTransition.prototype = Object.create(SetTransition.prototype);
NotSetTransition.prototype.constructor = NotSetTransition;
NotSetTransition.prototype.matches = function(symbol, minVocabSymbol, maxVocabSymbol) {
  return symbol >= minVocabSymbol && symbol <= maxVocabSymbol && !SetTransition.prototype.matches.call(this, symbol, minVocabSymbol, maxVocabSymbol);
};
NotSetTransition.prototype.toString = function() {
  return '~' + SetTransition.prototype.toString.call(this);
};
function WildcardTransition(target) {
  Transition.call(this, target);
  this.serializationType = Transition.WILDCARD;
  return this;
}
WildcardTransition.prototype = Object.create(Transition.prototype);
WildcardTransition.prototype.constructor = WildcardTransition;
WildcardTransition.prototype.matches = function(symbol, minVocabSymbol, maxVocabSymbol) {
  return symbol >= minVocabSymbol && symbol <= maxVocabSymbol;
};
WildcardTransition.prototype.toString = function() {
  return ".";
};
function PrecedencePredicateTransition(target, precedence) {
  AbstractPredicateTransition.call(this, target);
  this.serializationType = Transition.PRECEDENCE;
  this.precedence = precedence;
  this.isEpsilon = true;
  return this;
}
PrecedencePredicateTransition.prototype = Object.create(AbstractPredicateTransition.prototype);
PrecedencePredicateTransition.prototype.constructor = PrecedencePredicateTransition;
PrecedencePredicateTransition.prototype.matches = function(symbol, minVocabSymbol, maxVocabSymbol) {
  return false;
};
PrecedencePredicateTransition.prototype.getPredicate = function() {
  return new PrecedencePredicate(this.precedence);
};
PrecedencePredicateTransition.prototype.toString = function() {
  return this.precedence + " >= _p";
};
exports.Transition = Transition;
exports.AtomTransition = AtomTransition;
exports.SetTransition = SetTransition;
exports.NotSetTransition = NotSetTransition;
exports.RuleTransition = RuleTransition;
exports.ActionTransition = ActionTransition;
exports.EpsilonTransition = EpsilonTransition;
exports.RangeTransition = RangeTransition;
exports.WildcardTransition = WildcardTransition;
exports.PredicateTransition = PredicateTransition;
exports.PrecedencePredicateTransition = PrecedencePredicateTransition;
exports.AbstractPredicateTransition = AbstractPredicateTransition;
