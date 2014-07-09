/* jshint node:true, undef:true, unused:true */

var assert = require('assert');
var through = require('through');
var esprima = require('esprima');
var recast = require('recast');
var types = recast.types;
var n = types.namedTypes;
var b = types.builders;

var util = require('ast-util');

var Class = types.Type.or(n.ClassDeclaration, n.ClassExpression);

assert.ok(
  /harmony/.test(esprima.version),
  'looking for esprima harmony but found: ' + esprima.version
);

/**
 * Builds a function expression from an existing function, copying over the
 * properties that are not part of ast-types's build fields.
 *
 * @private
 * @param {ast-types.Node} fn
 * @return {ast-types.Node}
 */
function copyFunctionExpression(fn) {
  var result = b.functionExpression(
    fn.id,
    fn.params,
    fn.body,
    fn.generator,
    fn.expression
  );
  if ('async' in fn) {
    result.async = fn.async;
  }
  if ('defaults' in fn) {
    result.defaults = fn.defaults;
  }
  if ('rest' in fn) {
    result.rest = fn.rest;
  }
  return result;
}
// ES6 Working Draft 14.5.15
var DEFAULT_DESCRIPTORS = {
  default: {
    enumerable: b.literal(false),
    writable: b.literal(true)
  },

  get: {
    enumerable: b.literal(false)
  },

  set: {
    enumerable: b.literal(false)
  }
};

/**
 * Visits a `ClassDeclaration` node and replaces it with an equivalent node
 * with the class definition or expression turned into a function with
 * prototype properties for method definitions.
 *
 * @private
 * @param {Object} node
 * @this {ast-types.NodePath}
 */
function visitClassDeclaration(nodePath) {
  var node = nodePath.value;
  /*
   * All our definition statements go into an IIFE whose result goes into a
   * variable at the same scope as the original class.
   */
  nodePath.replace(b.variableDeclaration(
    'var',
    [b.variableDeclarator(
      node.id,
      generateClassDefinitionExpression.call(nodePath, node)
    )]
  ));
  this.traverse(nodePath);
}

/**
 * Visits a `ClassExpression` node and replaces it with an equivalent node
 * with the class definition or expression turned into a function with
 * prototype properties for method definitions.
 *
 * @private
 * @param {ast-types.ClassExpression} node
 * @this {ast-types.NodePath}
 */
function visitClassExpression(nodePath) {
  var node = nodePath.value;
  nodePath.replace(generateClassDefinitionExpression.call(nodePath, node));
  this.traverse(nodePath);
}

/**
 * Generates an expression that resolves to an equivalent function as the class
 * represented by `node`.
 *
 * @private
 * @param {ast-types.ClassDeclaration|ast-types.ClassExpression} node
 * @return {ast-types.Expression}
 * @this {ast-types.NodePath}
 */
function generateClassDefinitionExpression(node) {
  var body = node.body.body;
  var methodDefinitions = [];
  var propertyDescriptors = [];
  var propertyDescriptorMap = Object.create(null);
  var staticPropertyDescriptors = [];
  var staticPropertyDescriptorMap = Object.create(null);
  var constructor;

  var scope = this.scope;
  var globalScope = scope.getGlobalScope();
  var classId = node.id || util.uniqueIdentifier(scope);

  // Stash the specified or generated class id so super() can use it later.
  Object.defineProperty(node, 'CLASS_ID', {
    value: classId,
    enumerable: false
  });

  var superClassId = node.superClass && util.uniqueIdentifier(scope, 'super');

  function addPropertyDescriptor(property, key, value, isStatic) {
    var map = isStatic ? staticPropertyDescriptorMap : propertyDescriptorMap;
    var list = isStatic ? staticPropertyDescriptors : propertyDescriptors;

    if (!map[property]) {
      list.push({
        name: property,
        descriptor: map[property] = Object.create(
          DEFAULT_DESCRIPTORS[key] || DEFAULT_DESCRIPTORS.defaults
        )
      });
    }

    map[property][key] = value;
  }

  /**
   * Process each "method" definition. Methods, getters, setters, and the
   * constructor are all treated as method definitions.
   */
  body.forEach(function(statement) {
    if (n.MethodDefinition.check(statement)) {
      var fn = statement.value;
      var methodName = statement.key.name;

      if (methodName === 'constructor') {
        constructor = fn;
      } else if (statement.kind) {
        addPropertyDescriptor(
          methodName,
          statement.kind,
          copyFunctionExpression(statement.value)
        );
      } else {
        addPropertyDescriptor(
          methodName,
          'value',
          copyFunctionExpression(fn),
          statement.static
        );
      }
    }
  });

  if (!constructor) {
    var constructorBody = [];
    if (superClassId) {
      /**
       * There's no constructor, so build a default one that calls the super
       * class function with the instance as the context.
       *
       *   Object.getPrototypeOf(MyClass.prototype).constructor.apply(this, arguments)
       */
      var protoId = util.uniqueIdentifier(scope);

      constructorBody.push(
        // var $__0 = Object.getPrototypeOf(MyClass.prototype);
        b.variableDeclaration(
          'var',
          [b.variableDeclarator(
            protoId,
            util.callGetPrototypeOf(
              globalScope,
              b.memberExpression(classId, b.identifier('prototype'), false)
            )
          )]
        ),
        b.ifStatement(
          b.binaryExpression('!==', protoId, b.literal(null)),
          b.expressionStatement(
            b.callExpression(
              b.memberExpression(
                b.memberExpression(
                  protoId,
                  b.identifier('constructor'),
                  false
                ),
                b.identifier('apply'), false
              ),
              [b.thisExpression(), b.identifier('arguments')]
            )
          )
        )
      );
    }
    constructor = b.functionExpression(null, [], b.blockStatement(constructorBody));
  }

  /**
   * Define the constructor.
   *
   *   function MyClass() {}
   */
  var classDeclaration = b.functionDeclaration(
    classId,
    constructor.params,
    constructor.body
  );
  if ('rest' in constructor) {
    classDeclaration.rest = constructor.rest;
  }
  if ('defaults' in constructor) {
    classDeclaration.defaults = constructor.defaults;
  }
  var definitionStatements = [classDeclaration];

  if (superClassId) {
    /**
     * Set up inheritance.
     *
     *   MyClass.__proto__ = MySuper;
     *   MyClass.prototype = Object.create(MySuper.prototype);
     *   Object.defineProperty(MyClass.prototype, 'constructor', { value: MyClass });
     */
    definitionStatements.push(
      b.expressionStatement(b.assignmentExpression(
        '=',
        b.memberExpression(classId, b.identifier('__proto__'), false),
        b.conditionalExpression(
          b.binaryExpression('!==', superClassId, b.literal(null)),
          superClassId,
          b.memberExpression(b.identifier('Function'), b.identifier('prototype'), false)
        )
      )),
      b.expressionStatement(b.assignmentExpression(
        '=',
        b.memberExpression(classId, b.identifier('prototype'), false),
        util.callSharedMethod(
          globalScope,
          'Object.create',
          [b.conditionalExpression(
            b.binaryExpression('!==', superClassId, b.literal(null)),
            b.memberExpression(superClassId, b.identifier('prototype'), false),
            b.literal(null)
          )]
        )
      )),
      b.expressionStatement(util.callSharedMethod(
        globalScope,
        'Object.defineProperty',
        [
          b.memberExpression(classId, b.identifier('prototype'), false),
          b.literal('constructor'),
          b.objectExpression([b.property('init', b.identifier('value'), classId)])
        ]
      ))
    );
  }

  /**
   * Add the method definitions.
   *
   *   MyClass.prototype.toString = function(){};
   */
  definitionStatements.push.apply(definitionStatements, methodDefinitions);

  /**
   * Add methods, getters, and setters for the prototype and the class.
   *
   *   Object.defineProperty(MyClass.prototype, 'name', {
   *     get: function(){}
   *   });
   */
  addDefinePropertyDescriptorCalls(
    b.memberExpression(classId, b.identifier('prototype'), false),
    propertyDescriptors
  );

  addDefinePropertyDescriptorCalls(
    classId,
    staticPropertyDescriptors
  );

  /**
   * Add calls to `Object.defineProperty` with the given descriptor information
   * on the given object. This is used to add properties to the "class" itself
   * (static properties) and its prototype (instance properties).
   *
   * @private
   */
  function addDefinePropertyDescriptorCalls(object, descriptors) {
    descriptors.forEach(function(propertyDescriptor) {
      var descriptorObjectProperties = [];
      for (var key in propertyDescriptor.descriptor) {
        var value = propertyDescriptor.descriptor[key];
        descriptorObjectProperties.push(b.property('init', b.identifier(key), value));
      }

      definitionStatements.push(b.expressionStatement(util.callSharedMethod(
        globalScope,
        'Object.defineProperty',
        [
          object,
          b.literal(propertyDescriptor.name),
          b.objectExpression(descriptorObjectProperties)
        ]
      )));
    });
  }

  /**
   * Finally, return the constructor from the IIFE.
   */
  definitionStatements.push(b.returnStatement(classId));

  /*
   * All our definition statements go into an IIFE that takes the superclass
   * and returns the class.
   */
  return transform(b.callExpression(
    b.functionExpression(
      null,
      superClassId ? [superClassId] : [],
      b.blockStatement(definitionStatements),
      false, true, false
    ),
    superClassId ? [node.superClass] : []
  ));
}

/**
 * Finds a parent node of the correct type and returns it. Returns null if no
 * such node is found.
 *
 * @private
 * @param {ast-types.Node} node
 * @param {ast-types.NodePath} path
 * @param {ast-types.Type} type
 * @return {?ast-types.Node}
 */
function getEnclosingNodeOfType(node, path, type) {
  var ancestor = path;

  while (ancestor) {
    if (type.check(ancestor.node)) {
      return ancestor.node;
    }
    ancestor = ancestor.parent;
  }

  return null;
}

/**
 * Visits a `CallExpression` node which calls `super()` and replaces it with a
 * call to the current method on the superclass for the containing class.
 *
 * @private
 * @param {Object} node
 * @this {ast-types.NodePath}
 */
function visitSuperCall(nodePath) {
  var node = nodePath.value;
  var classNode = getEnclosingNodeOfType(node, nodePath, Class);
  var methodDefinition = getEnclosingNodeOfType(node, nodePath, n.MethodDefinition);

  if (classNode && methodDefinition) {
    // Replace `super()` with `Object.getPrototypeOf(MyClass[.prototype]).myMethod.call(this)`.
    var context = methodDefinition.static ?
      classNode.CLASS_ID :
      b.memberExpression(classNode.CLASS_ID, b.identifier('prototype'), false);

    nodePath.replace(b.callExpression(
      b.memberExpression(
        b.memberExpression(
          util.callGetPrototypeOf(
            nodePath.scope.getGlobalScope(),
            context
          ),
          methodDefinition.key,
          false
        ),
        b.identifier('call'),
        false
      ),
      [b.thisExpression()].concat(node.arguments)
    ));
    this.traverse(nodePath);
  } else {
    this.traverse(nodePath);
  }
}

/**
 * @private
 */
function visitSuperMemberExpression(nodePath) {
  var node = nodePath.value;
  var classNode = getEnclosingNodeOfType(node, nodePath, Class);

  if (classNode) {
    var globalScope = nodePath.scope.getGlobalScope();
    // Replace `super.foo` with an expression that returns the value of the
    // `foo` property as evaluated by the superclass with the current `this`
    // context.
    nodePath.replace(util.callGet(
      globalScope,
      util.callGetPrototypeOf(
        globalScope,
        b.memberExpression(
          classNode.CLASS_ID,
          b.identifier('prototype'),
          false
        )
      ),
      b.literal(node.property.name),
      b.thisExpression()
    ));
  }
  this.traverse(nodePath);
}

/**
 * @private
 */
function visitSuperCallMemberExpression(nodePath) {
  var node = nodePath.value;
  var classNode = getEnclosingNodeOfType(node, nodePath, Class);

  if (classNode) {
    var globalScope = nodePath.scope.getGlobalScope();
    // Replace `super.foo()` with an expression that calls the value of the
    // `foo` property as evaluated by the superclass with the current `this`
    // context.
    nodePath.replace(b.callExpression(
      b.memberExpression(
        util.callGet(
          globalScope,
          util.callGetPrototypeOf(
            globalScope,
            b.memberExpression(
              classNode.CLASS_ID,
              b.identifier('prototype'),
              false
            )
          ),
          b.literal(node.callee.property.name),
          b.thisExpression()
        ),
        b.identifier('call'),
        false
      ),
      [b.thisExpression()].concat(node.arguments)
    ));
  }
  this.traverse(nodePath);
}

function visitCallExpression(nodePath) {
  var node = nodePath.value;
  if (n.Identifier.check(node.callee) && node.callee.name === 'super') {
    // super()
    visitSuperCall.call(this, nodePath);
  } else if (n.MemberExpression.check(node.callee) && n.Identifier.check(node.callee.object) && node.callee.object.name === 'super') {
    // super.foo()
    visitSuperCallMemberExpression.call(this, nodePath);
  } else {
    this.traverse(nodePath);
  }
}

function visitMemberExpression(nodePath) {
  var node = nodePath.value;
  if (n.Identifier.check(node.object) && node.object.name === 'super') {
    visitSuperMemberExpression.call(this, nodePath);
  } else {
    this.traverse(nodePath);
  }
}

var visitors = {
  visitClassDeclaration: visitClassDeclaration,
  visitClassExpression: visitClassExpression,
  visitCallExpression: visitCallExpression,
  visitMemberExpression: visitMemberExpression
};


/**
 * Transform an Esprima AST generated from ES6 by replacing all
 * classes with an equivalent approach in ES5.
 *
 * NOTE: The argument may be modified by this function. To prevent modification
 * of your AST, pass a copy instead of a direct reference:
 *
 *   // instead of transform(ast), pass a copy
 *   transform(JSON.parse(JSON.stringify(ast));
 *
 * @param {Object} ast
 * @return {Object}
 */
function transform(ast) {
  return recast.visit(ast, visitors);
  //return types.traverse(ast, visitNode);
}

module.exports.compile = function(source, pretty) {
  var ast = recast.parse(source, {esprima: esprima});
  if (pretty) {
    return recast.prettyPrint(transform(ast));
  }
  return recast.print(transform(ast));
};

module.exports.parse = function(source) {
  return transform(recast.parse(source, {esprima: esprima}));
};

module.exports.transform = transform;
module.exports.visitors = visitors;
