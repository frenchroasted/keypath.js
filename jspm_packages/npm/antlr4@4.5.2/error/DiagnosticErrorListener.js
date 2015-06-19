/* */ 
var BitSet = require("../Utils").BitSet;
var ErrorListener = require("./ErrorListener").ErrorListener;
var Interval = require("../IntervalSet").Interval;
function DiagnosticErrorListener(exactOnly) {
  ErrorListener.call(this);
  exactOnly = exactOnly || true;
  this.exactOnly = exactOnly;
  return this;
}
DiagnosticErrorListener.prototype = Object.create(ErrorListener.prototype);
DiagnosticErrorListener.prototype.constructor = DiagnosticErrorListener;
DiagnosticErrorListener.prototype.reportAmbiguity = function(recognizer, dfa, startIndex, stopIndex, exact, ambigAlts, configs) {
  if (this.exactOnly && !exact) {
    return ;
  }
  var msg = "reportAmbiguity d=" + this.getDecisionDescription(recognizer, dfa) + ": ambigAlts=" + this.getConflictingAlts(ambigAlts, configs) + ", input='" + recognizer.getTokenStream().getText(new Interval(startIndex, stopIndex)) + "'";
  recognizer.notifyErrorListeners(msg);
};
DiagnosticErrorListener.prototype.reportAttemptingFullContext = function(recognizer, dfa, startIndex, stopIndex, conflictingAlts, configs) {
  var msg = "reportAttemptingFullContext d=" + this.getDecisionDescription(recognizer, dfa) + ", input='" + recognizer.getTokenStream().getText(new Interval(startIndex, stopIndex)) + "'";
  recognizer.notifyErrorListeners(msg);
};
DiagnosticErrorListener.prototype.reportContextSensitivity = function(recognizer, dfa, startIndex, stopIndex, prediction, configs) {
  var msg = "reportContextSensitivity d=" + this.getDecisionDescription(recognizer, dfa) + ", input='" + recognizer.getTokenStream().getText(new Interval(startIndex, stopIndex)) + "'";
  recognizer.notifyErrorListeners(msg);
};
DiagnosticErrorListener.prototype.getDecisionDescription = function(recognizer, dfa) {
  var decision = dfa.decision;
  var ruleIndex = dfa.atnStartState.ruleIndex;
  var ruleNames = recognizer.ruleNames;
  if (ruleIndex < 0 || ruleIndex >= ruleNames.length) {
    return "" + decision;
  }
  var ruleName = ruleNames[ruleIndex] || null;
  if (ruleName === null || ruleName.length === 0) {
    return "" + decision;
  }
  return "" + decision + " (" + ruleName + ")";
};
DiagnosticErrorListener.prototype.getConflictingAlts = function(reportedAlts, configs) {
  if (reportedAlts !== null) {
    return reportedAlts;
  }
  var result = new BitSet();
  for (var i = 0; i < configs.items.length; i++) {
    result.add(configs.items[i].alt);
  }
  return "{" + result.values().join(", ") + "}";
};
exports.DiagnosticErrorListener = DiagnosticErrorListener;
