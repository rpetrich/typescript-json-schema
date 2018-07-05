"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const glob = require("glob");
const stringify = require("json-stable-stringify");
const path = require("path");
const ts = require("typescript");
const vm = require("vm");
const REGEX_FILE_NAME_OR_SPACE = /(\bimport\(".*?"\)|".*?")\.| /g;
const REGEX_TSCONFIG_NAME = /^.*\.json$/;
const REGEX_TJS_JSDOC = /^-([\w]+)\s+(\S|\S[\s\S]*\S)\s*$/g;
function getDefaultArgs() {
    return {
        ref: true,
        aliasRef: false,
        topRef: false,
        titles: false,
        defaultProps: false,
        noExtraProps: false,
        propOrder: false,
        typeOfKeyword: false,
        required: false,
        strictNullChecks: false,
        ignoreErrors: false,
        out: "",
        validationKeywords: [],
        include: [],
        excludePrivate: false,
        uniqueNames: false,
        rejectDateType: false,
    };
}
exports.getDefaultArgs = getDefaultArgs;
function extend(target, ..._) {
    if (target == null) {
        throw new TypeError("Cannot convert undefined or null to object");
    }
    const to = Object(target);
    for (var index = 1; index < arguments.length; index++) {
        const nextSource = arguments[index];
        if (nextSource != null) {
            for (const nextKey in nextSource) {
                if (Object.prototype.hasOwnProperty.call(nextSource, nextKey)) {
                    to[nextKey] = nextSource[nextKey];
                }
            }
        }
    }
    return to;
}
function unique(arr) {
    const temp = {};
    for (const e of arr) {
        temp[e] = true;
    }
    const r = [];
    for (const k in temp) {
        if (Object.prototype.hasOwnProperty.call(temp, k)) {
            r.push(k);
        }
    }
    return r;
}
function parseValue(value) {
    try {
        return JSON.parse(value);
    }
    catch (error) {
        return value;
    }
}
function extractLiteralValue(typ) {
    let str = typ.value;
    if (str === undefined) {
        str = typ.text;
    }
    if (typ.flags & ts.TypeFlags.StringLiteral) {
        return str;
    }
    else if (typ.flags & ts.TypeFlags.BooleanLiteral) {
        return typ.intrinsicName === "true";
    }
    else if (typ.flags & ts.TypeFlags.EnumLiteral) {
        const num = parseFloat(str);
        return isNaN(num) ? str : num;
    }
    else if (typ.flags & ts.TypeFlags.NumberLiteral) {
        return parseFloat(str);
    }
    return undefined;
}
function resolveTupleType(propertyType) {
    if (!propertyType.getSymbol() && (propertyType.getFlags() & ts.TypeFlags.Object && propertyType.objectFlags & ts.ObjectFlags.Reference)) {
        return propertyType.target;
    }
    if (!(propertyType.getFlags() & ts.TypeFlags.Object && propertyType.objectFlags & ts.ObjectFlags.Tuple)) {
        return null;
    }
    return propertyType;
}
const simpleTypesAllowedProperties = {
    type: true,
    description: true
};
function addSimpleType(def, type) {
    for (const k in def) {
        if (!simpleTypesAllowedProperties[k]) {
            return false;
        }
    }
    if (!def.type) {
        def.type = type;
    }
    else if (typeof def.type !== "string") {
        if (!def.type.every((val) => { return typeof val === "string"; })) {
            return false;
        }
        if (def.type.indexOf("null") === -1) {
            def.type.push("null");
        }
    }
    else {
        if (typeof def.type !== "string") {
            return false;
        }
        if (def.type !== "null") {
            def.type = [def.type, "null"];
        }
    }
    return true;
}
function makeNullable(def) {
    if (!addSimpleType(def, "null")) {
        const union = def.oneOf || def.anyOf;
        if (union) {
            union.push({ type: "null" });
        }
        else {
            const subdef = {};
            for (var k in def) {
                if (def.hasOwnProperty(k)) {
                    subdef[k] = def[k];
                    delete def[k];
                }
            }
            def.anyOf = [subdef, { type: "null" }];
        }
    }
    return def;
}
const validationKeywords = {
    multipleOf: true,
    maximum: true,
    exclusiveMaximum: true,
    minimum: true,
    exclusiveMinimum: true,
    maxLength: true,
    minLength: true,
    pattern: true,
    maxItems: true,
    minItems: true,
    uniqueItems: true,
    maxProperties: true,
    minProperties: true,
    additionalProperties: true,
    enum: true,
    type: true,
    ignore: true,
    description: true,
    format: true,
    default: true,
    $ref: true,
    id: true
};
class JsonSchemaGenerator {
    constructor(symbols, allSymbols, userSymbols, inheritingTypes, tc, args = {}) {
        this.reffedDefinitions = {};
        this.typeNamesById = {};
        this.typeNamesUsed = {};
        this.args = Object.assign(getDefaultArgs(), args);
        this.symbols = symbols;
        this.allSymbols = allSymbols;
        this.userSymbols = userSymbols;
        this.inheritingTypes = inheritingTypes;
        this.tc = tc;
        this.userValidationKeywords = this.args.validationKeywords.reduce((acc, word) => (Object.assign({}, acc, { [word]: true })), {});
    }
    get ReffedDefinitions() {
        return this.reffedDefinitions;
    }
    parseCommentsIntoDefinition(symbol, definition, otherAnnotations) {
        if (!symbol) {
            return;
        }
        const comments = symbol.getDocumentationComment(this.tc);
        if (comments.length) {
            definition.description = comments.map(comment => comment.kind === "lineBreak" ? comment.text : comment.text.trim().replace(/\r\n/g, "\n")).join("");
        }
        const jsdocs = symbol.getJsDocTags();
        jsdocs.forEach(doc => {
            const [name, text] = (doc.name === "TJS" ? new RegExp(REGEX_TJS_JSDOC).exec(doc.text).slice(1, 3) : [doc.name, doc.text]);
            if (validationKeywords[name] || this.userValidationKeywords[name]) {
                definition[name] = text === undefined ? "" : parseValue(text);
            }
            else {
                otherAnnotations[doc.name] = true;
            }
        });
    }
    getDefinitionForRootType(propertyType, reffedType, definition) {
        const tupleType = resolveTupleType(propertyType);
        if (tupleType) {
            const elemTypes = tupleType.elementTypes || propertyType.typeArguments;
            const fixedTypes = elemTypes.map(elType => this.getTypeDefinition(elType));
            definition.type = "array";
            definition.items = fixedTypes;
            definition.minItems = fixedTypes.length;
            definition.additionalItems = {
                anyOf: fixedTypes
            };
        }
        else {
            const propertyTypeString = this.tc.typeToString(propertyType, undefined, ts.TypeFormatFlags.UseFullyQualifiedType);
            const flags = propertyType.flags;
            const arrayType = this.tc.getIndexTypeOfType(propertyType, ts.IndexKind.Number);
            if (flags & ts.TypeFlags.String) {
                definition.type = "string";
            }
            else if (flags & ts.TypeFlags.Number) {
                const isInteger = (definition.type === "integer" || (reffedType && reffedType.getName() === "integer"));
                definition.type = isInteger ? "integer" : "number";
            }
            else if (flags & ts.TypeFlags.Boolean) {
                definition.type = "boolean";
            }
            else if (flags & ts.TypeFlags.Null) {
                definition.type = "null";
            }
            else if (flags & ts.TypeFlags.Undefined) {
                definition.type = "undefined";
            }
            else if (flags & ts.TypeFlags.Any) {
            }
            else if (propertyTypeString === "Date" && !this.args.rejectDateType) {
                definition.type = "string";
                definition.format = "date-time";
            }
            else if (propertyTypeString === "object") {
                definition.type = "object";
                definition.properties = {};
                definition.additionalProperties = true;
            }
            else {
                const value = extractLiteralValue(propertyType);
                if (value !== undefined) {
                    definition.type = typeof value;
                    definition.enum = [value];
                }
                else if (arrayType !== undefined) {
                    definition.type = "array";
                    definition.items = this.getTypeDefinition(arrayType);
                }
                else {
                    const error = new TypeError("Unsupported type: " + propertyTypeString);
                    error.type = propertyType;
                    throw error;
                }
            }
        }
        return definition;
    }
    getReferencedTypeSymbol(prop) {
        const decl = prop.getDeclarations();
        if (decl && decl.length) {
            const type = decl[0].type;
            if (type && (type.kind & ts.SyntaxKind.TypeReference) && type.typeName) {
                return this.tc.getSymbolAtLocation(type.typeName);
            }
        }
        return undefined;
    }
    getDefinitionForProperty(prop, node) {
        if (prop.flags & ts.SymbolFlags.Method) {
            return null;
        }
        const propertyName = prop.getName();
        const propertyType = this.tc.getTypeOfSymbolAtLocation(prop, node);
        const reffedType = this.getReferencedTypeSymbol(prop);
        const definition = this.getTypeDefinition(propertyType, undefined, undefined, prop, reffedType);
        if (this.args.titles) {
            definition.title = propertyName;
        }
        if (definition.hasOwnProperty("ignore")) {
            return null;
        }
        const valDecl = prop.valueDeclaration;
        if (valDecl && valDecl.initializer) {
            let initial = valDecl.initializer;
            while (ts.isTypeAssertion(initial)) {
                initial = initial.expression;
            }
            if (initial.expression) {
                console.warn("initializer is expression for property " + propertyName);
            }
            else if (initial.kind && initial.kind === ts.SyntaxKind.NoSubstitutionTemplateLiteral) {
                definition.default = initial.getText();
            }
            else {
                try {
                    const sandbox = { sandboxvar: null };
                    vm.runInNewContext("sandboxvar=" + initial.getText(), sandbox);
                    const val = sandbox.sandboxvar;
                    if (val === null || typeof val === "string" || typeof val === "number" || typeof val === "boolean" || Object.prototype.toString.call(val) === "[object Array]") {
                        definition.default = val;
                    }
                    else if (val) {
                        console.warn("unknown initializer for property " + propertyName + ": " + val);
                    }
                }
                catch (e) {
                    console.warn("exception evaluating initializer for property " + propertyName);
                }
            }
        }
        return definition;
    }
    getEnumDefinition(clazzType, definition) {
        const node = clazzType.getSymbol().getDeclarations()[0];
        const fullName = this.tc.typeToString(clazzType, undefined, ts.TypeFormatFlags.UseFullyQualifiedType);
        const members = node.kind === ts.SyntaxKind.EnumDeclaration ?
            node.members :
            ts.createNodeArray([node]);
        var enumValues = [];
        const enumTypes = [];
        const addType = (type) => {
            if (enumTypes.indexOf(type) === -1) {
                enumTypes.push(type);
            }
        };
        members.forEach(member => {
            const caseLabel = member.name.text;
            const constantValue = this.tc.getConstantValue(member);
            if (constantValue !== undefined) {
                enumValues.push(constantValue);
                addType(typeof constantValue);
            }
            else {
                const initial = member.initializer;
                if (initial) {
                    if (initial.expression) {
                        const exp = initial.expression;
                        const text = exp.text;
                        if (text) {
                            enumValues.push(text);
                            addType("string");
                        }
                        else if (exp.kind === ts.SyntaxKind.TrueKeyword || exp.kind === ts.SyntaxKind.FalseKeyword) {
                            enumValues.push((exp.kind === ts.SyntaxKind.TrueKeyword));
                            addType("boolean");
                        }
                        else {
                            console.warn("initializer is expression for enum: " + fullName + "." + caseLabel);
                        }
                    }
                    else if (initial.kind === ts.SyntaxKind.NoSubstitutionTemplateLiteral) {
                        enumValues.push(initial.getText());
                        addType("string");
                    }
                    else if (initial.kind === ts.SyntaxKind.NullKeyword) {
                        enumValues.push(null);
                        addType("null");
                    }
                }
            }
        });
        if (enumTypes.length) {
            definition.type = (enumTypes.length === 1) ? enumTypes[0] : enumTypes;
        }
        if (enumValues.length > 0) {
            definition.enum = enumValues.sort();
        }
        return definition;
    }
    getUnionDefinition(unionType, prop, unionModifier, definition) {
        const enumValues = [];
        const simpleTypes = [];
        const schemas = [];
        const pushSimpleType = (type) => {
            if (simpleTypes.indexOf(type) === -1) {
                simpleTypes.push(type);
            }
        };
        const pushEnumValue = (val) => {
            if (enumValues.indexOf(val) === -1) {
                enumValues.push(val);
            }
        };
        for (const valueType of unionType.types) {
            const value = extractLiteralValue(valueType);
            if (value !== undefined) {
                pushEnumValue(value);
            }
            else {
                const def = this.getTypeDefinition(valueType);
                if (def.type === "undefined") {
                    if (prop) {
                        prop.mayBeUndefined = true;
                    }
                }
                else {
                    const keys = Object.keys(def);
                    if (keys.length === 1 && keys[0] === "type") {
                        if (typeof def.type !== "string") {
                            console.error("Expected only a simple type.");
                        }
                        else {
                            pushSimpleType(def.type);
                        }
                    }
                    else {
                        schemas.push(def);
                    }
                }
            }
        }
        if (enumValues.length > 0) {
            const isOnlyBooleans = enumValues.length === 2 &&
                typeof enumValues[0] === "boolean" &&
                typeof enumValues[1] === "boolean" &&
                enumValues[0] !== enumValues[1];
            if (isOnlyBooleans) {
                pushSimpleType("boolean");
            }
            else {
                const enumSchema = { enum: enumValues.sort() };
                if (enumValues.every((x) => { return typeof x === "string"; })) {
                    enumSchema.type = "string";
                }
                else if (enumValues.every((x) => { return typeof x === "number"; })) {
                    enumSchema.type = "number";
                }
                else if (enumValues.every((x) => { return typeof x === "boolean"; })) {
                    enumSchema.type = "boolean";
                }
                schemas.push(enumSchema);
            }
        }
        if (simpleTypes.length > 0) {
            schemas.push({ type: simpleTypes.length === 1 ? simpleTypes[0] : simpleTypes });
        }
        if (schemas.length === 1) {
            for (const k in schemas[0]) {
                if (schemas[0].hasOwnProperty(k)) {
                    definition[k] = schemas[0][k];
                }
            }
        }
        else {
            definition[unionModifier] = schemas;
        }
        return definition;
    }
    getIntersectionDefinition(intersectionType, definition) {
        const simpleTypes = [];
        const schemas = [];
        const pushSimpleType = (type) => {
            if (simpleTypes.indexOf(type) === -1) {
                simpleTypes.push(type);
            }
        };
        for (const intersectionMember of intersectionType.types) {
            const def = this.getTypeDefinition(intersectionMember);
            if (def.type === "undefined") {
                console.error("Undefined in intersection makes no sense.");
            }
            else {
                const keys = Object.keys(def);
                if (keys.length === 1 && keys[0] === "type") {
                    if (typeof def.type !== "string") {
                        console.error("Expected only a simple type.");
                    }
                    else {
                        pushSimpleType(def.type);
                    }
                }
                else {
                    schemas.push(def);
                }
            }
        }
        if (simpleTypes.length > 0) {
            schemas.push({ type: simpleTypes.length === 1 ? simpleTypes[0] : simpleTypes });
        }
        if (schemas.length === 1) {
            for (const k in schemas[0]) {
                if (schemas[0].hasOwnProperty(k)) {
                    definition[k] = schemas[0][k];
                }
            }
        }
        else {
            definition.allOf = schemas;
        }
        return definition;
    }
    getClassDefinition(clazzType, definition) {
        const node = clazzType.getSymbol().getDeclarations()[0];
        if (this.args.typeOfKeyword && node.kind === ts.SyntaxKind.FunctionType) {
            definition.typeof = "function";
            return definition;
        }
        const clazz = node;
        const props = this.tc.getPropertiesOfType(clazzType).filter(prop => {
            if (!this.args.excludePrivate) {
                return true;
            }
            const decls = prop.declarations;
            return !(decls && decls.filter(decl => {
                const mods = decl.modifiers;
                return mods && mods.filter(mod => mod.kind === ts.SyntaxKind.PrivateKeyword).length > 0;
            }).length > 0);
        });
        const fullName = this.tc.typeToString(clazzType, undefined, ts.TypeFormatFlags.UseFullyQualifiedType);
        const modifierFlags = ts.getCombinedModifierFlags(node);
        if (modifierFlags & ts.ModifierFlags.Abstract) {
            const oneOf = this.inheritingTypes[fullName].map((typename) => {
                return this.getTypeDefinition(this.allSymbols[typename]);
            });
            definition.oneOf = oneOf;
        }
        else {
            if (clazz.members) {
                const indexSignatures = clazz.members == null ? [] : clazz.members.filter(x => x.kind === ts.SyntaxKind.IndexSignature);
                if (indexSignatures.length === 1) {
                    const indexSignature = indexSignatures[0];
                    if (indexSignature.parameters.length !== 1) {
                        throw new Error("Not supported: IndexSignatureDeclaration parameters.length != 1");
                    }
                    const indexSymbol = indexSignature.parameters[0].symbol;
                    const indexType = this.tc.getTypeOfSymbolAtLocation(indexSymbol, node);
                    const isStringIndexed = (indexType.flags === ts.TypeFlags.String);
                    if (indexType.flags !== ts.TypeFlags.Number && !isStringIndexed) {
                        throw new Error("Not supported: IndexSignatureDeclaration with index symbol other than a number or a string");
                    }
                    const typ = this.tc.getTypeAtLocation(indexSignature.type);
                    const def = this.getTypeDefinition(typ, undefined, "anyOf");
                    if (isStringIndexed) {
                        definition.type = "object";
                        definition.additionalProperties = def;
                    }
                    else {
                        definition.type = "array";
                        definition.items = def;
                    }
                }
            }
            const propertyDefinitions = props.reduce((all, prop) => {
                const propertyName = prop.getName();
                const propDef = this.getDefinitionForProperty(prop, node);
                if (propDef != null) {
                    all[propertyName] = propDef;
                }
                return all;
            }, {});
            if (definition.type === undefined) {
                definition.type = "object";
            }
            if (definition.type === "object" && Object.keys(propertyDefinitions).length > 0) {
                definition.properties = propertyDefinitions;
            }
            if (this.args.defaultProps) {
                definition.defaultProperties = [];
            }
            if (this.args.noExtraProps && definition.additionalProperties === undefined) {
                definition.additionalProperties = false;
            }
            if (this.args.propOrder) {
                const propertyOrder = props.reduce((order, prop) => {
                    order.push(prop.getName());
                    return order;
                }, []);
                definition.propertyOrder = propertyOrder;
            }
            if (this.args.required) {
                const requiredProps = props.reduce((required, prop) => {
                    const def = {};
                    this.parseCommentsIntoDefinition(prop, def, {});
                    if (!(prop.flags & ts.SymbolFlags.Optional) && !(prop.flags & ts.SymbolFlags.Method) && !prop.mayBeUndefined && !def.hasOwnProperty("ignore")) {
                        required.push(prop.getName());
                    }
                    return required;
                }, []);
                if (requiredProps.length > 0) {
                    definition.required = unique(requiredProps).sort();
                }
            }
        }
        return definition;
    }
    getTypeName(typ) {
        const id = typ.id;
        if (this.typeNamesById[id]) {
            return this.typeNamesById[id];
        }
        const baseName = this.tc.typeToString(typ, undefined, ts.TypeFormatFlags.NoTruncation | ts.TypeFormatFlags.UseFullyQualifiedType).replace(REGEX_FILE_NAME_OR_SPACE, "");
        let name = baseName;
        if (this.typeNamesUsed[name]) {
            for (let i = 1; true; ++i) {
                name = baseName + "_" + i;
                if (!this.typeNamesUsed[name]) {
                    break;
                }
            }
        }
        this.typeNamesById[id] = name;
        this.typeNamesUsed[name] = true;
        return name;
    }
    getTypeDefinition(typ, asRef = this.args.ref, unionModifier = "anyOf", prop, reffedType, pairedSymbol) {
        const definition = {};
        while (typ.aliasSymbol && (typ.aliasSymbol.escapedName === "Readonly" || typ.aliasSymbol.escapedName === "Mutable") && typ.aliasTypeArguments && typ.aliasTypeArguments[0]) {
            typ = typ.aliasTypeArguments[0];
            reffedType = undefined;
        }
        if (this.args.typeOfKeyword && (typ.flags & ts.TypeFlags.Object) && (typ.objectFlags & ts.ObjectFlags.Anonymous)) {
            definition.typeof = "function";
            return definition;
        }
        let returnedDefinition = definition;
        const symbol = typ.getSymbol();
        const isRawType = (!symbol || symbol.name === "Date" || symbol.name === "integer" || this.tc.getIndexInfoOfType(typ, ts.IndexKind.Number) !== undefined);
        let isStringEnum = false;
        if (typ.flags & ts.TypeFlags.Union) {
            const unionType = typ;
            isStringEnum = (unionType.types.every(propType => {
                return (propType.getFlags() & ts.TypeFlags.StringLiteral) !== 0;
            }));
        }
        const asTypeAliasRef = asRef && reffedType && (this.args.aliasRef || isStringEnum);
        if (!asTypeAliasRef) {
            if (isRawType || typ.getFlags() & ts.TypeFlags.Object && typ.objectFlags & ts.ObjectFlags.Anonymous) {
                asRef = false;
            }
        }
        let fullTypeName = "";
        if (asTypeAliasRef) {
            fullTypeName = this.tc.getFullyQualifiedName(reffedType.getFlags() & ts.SymbolFlags.Alias ?
                this.tc.getAliasedSymbol(reffedType) :
                reffedType).replace(REGEX_FILE_NAME_OR_SPACE, "");
        }
        else if (asRef) {
            fullTypeName = this.getTypeName(typ);
        }
        if (asRef) {
            returnedDefinition = {
                $ref: "#/definitions/" + fullTypeName
            };
        }
        const otherAnnotations = {};
        this.parseCommentsIntoDefinition(reffedType, definition, otherAnnotations);
        if (prop) {
            this.parseCommentsIntoDefinition(prop, returnedDefinition, otherAnnotations);
        }
        this.parseCommentsIntoDefinition(symbol, definition, otherAnnotations);
        if (!asRef || !this.reffedDefinitions[fullTypeName]) {
            if (asRef) {
                let reffedDefinition;
                if (asTypeAliasRef && reffedType.getFlags() & (ts.TypeFlags.IndexedAccess | ts.TypeFlags.Index) && symbol) {
                    reffedDefinition = this.getTypeDefinition(typ, true, undefined, symbol, symbol);
                }
                else {
                    reffedDefinition = definition;
                }
                this.reffedDefinitions[fullTypeName] = reffedDefinition;
                if (this.args.titles && fullTypeName) {
                    definition.title = fullTypeName;
                }
            }
            const node = symbol && symbol.getDeclarations() !== undefined ? symbol.getDeclarations()[0] : null;
            if (definition.type === undefined) {
                if (typ.flags & ts.TypeFlags.Union) {
                    this.getUnionDefinition(typ, prop, unionModifier, definition);
                }
                else if (typ.flags & ts.TypeFlags.Intersection) {
                    if (this.args.noExtraProps) {
                        if (this.args.noExtraProps) {
                            definition.additionalProperties = false;
                        }
                        const types = typ.types;
                        for (const member of types) {
                            const other = this.getTypeDefinition(member, false);
                            definition.type = other.type;
                            definition.properties = extend(definition.properties || {}, other.properties);
                            if (Object.keys(other.default || {}).length > 0) {
                                definition.default = extend(definition.default || {}, other.default);
                            }
                            if (other.required) {
                                definition.required = unique((definition.required || []).concat(other.required)).sort();
                            }
                        }
                    }
                    else {
                        this.getIntersectionDefinition(typ, definition);
                    }
                }
                else if (isRawType) {
                    if (pairedSymbol) {
                        this.parseCommentsIntoDefinition(pairedSymbol, definition, {});
                    }
                    this.getDefinitionForRootType(typ, reffedType, definition);
                }
                else if (node && (node.kind === ts.SyntaxKind.EnumDeclaration || node.kind === ts.SyntaxKind.EnumMember)) {
                    this.getEnumDefinition(typ, definition);
                }
                else if (symbol && symbol.flags & ts.SymbolFlags.TypeLiteral && symbol.members.size === 0 && !(node && (node.kind === ts.SyntaxKind.MappedType))) {
                    definition.type = "object";
                    definition.properties = {};
                }
                else {
                    this.getClassDefinition(typ, definition);
                }
            }
        }
        if (otherAnnotations["nullable"]) {
            makeNullable(returnedDefinition);
        }
        return returnedDefinition;
    }
    setSchemaOverride(symbolName, schema) {
        this.reffedDefinitions[symbolName] = schema;
    }
    getSchemaForSymbol(symbolName, includeReffedDefinitions = true) {
        if (!this.allSymbols[symbolName]) {
            throw new Error(`type ${symbolName} not found`);
        }
        const def = this.getTypeDefinition(this.allSymbols[symbolName], this.args.topRef, undefined, undefined, undefined, this.userSymbols[symbolName] || undefined);
        if (this.args.ref && includeReffedDefinitions && Object.keys(this.reffedDefinitions).length > 0) {
            def.definitions = this.reffedDefinitions;
        }
        def["$schema"] = "http://json-schema.org/draft-06/schema#";
        return def;
    }
    getSchemaForSymbols(symbolNames, includeReffedDefinitions = true) {
        const root = {
            $schema: "http://json-schema.org/draft-06/schema#",
            definitions: {}
        };
        for (const symbolName of symbolNames) {
            root.definitions[symbolName] = this.getTypeDefinition(this.allSymbols[symbolName], this.args.topRef, undefined, undefined, undefined, this.userSymbols[symbolName]);
        }
        if (this.args.ref && includeReffedDefinitions && Object.keys(this.reffedDefinitions).length > 0) {
            root.definitions = Object.assign({}, root.definitions, this.reffedDefinitions);
        }
        return root;
    }
    getSymbols(name) {
        if (name === void 0) {
            return this.symbols;
        }
        return this.symbols.filter(symbol => symbol.typeName === name);
    }
    getUserSymbols() {
        return Object.keys(this.userSymbols);
    }
    getMainFileSymbols(program, onlyIncludeFiles) {
        function includeFile(file) {
            if (onlyIncludeFiles === undefined) {
                return !file.isDeclarationFile;
            }
            return onlyIncludeFiles.indexOf(file.fileName) >= 0;
        }
        const files = program.getSourceFiles().filter(includeFile);
        if (files.length) {
            return Object.keys(this.userSymbols).filter((key) => {
                const symbol = this.userSymbols[key];
                if (!symbol || !symbol.declarations || !symbol.declarations.length) {
                    return false;
                }
                let node = symbol.declarations[0];
                while (node && node.parent) {
                    node = node.parent;
                }
                return files.indexOf(node.getSourceFile()) > -1;
            });
        }
        return [];
    }
}
exports.JsonSchemaGenerator = JsonSchemaGenerator;
function getProgramFromFiles(files, jsonCompilerOptions = {}, basePath = "./") {
    const compilerOptions = ts.convertCompilerOptionsFromJson(jsonCompilerOptions, basePath).options;
    const options = {
        noEmit: true, emitDecoratorMetadata: true, experimentalDecorators: true, target: ts.ScriptTarget.ES5, module: ts.ModuleKind.CommonJS, allowUnusedLabels: true,
    };
    for (const k in compilerOptions) {
        if (compilerOptions.hasOwnProperty(k)) {
            options[k] = compilerOptions[k];
        }
    }
    return ts.createProgram(files, options);
}
exports.getProgramFromFiles = getProgramFromFiles;
function buildGenerator(program, args = {}, onlyIncludeFiles) {
    function isUserFile(file) {
        if (onlyIncludeFiles === undefined) {
            return !file.hasNoDefaultLib;
        }
        return onlyIncludeFiles.indexOf(file.fileName) >= 0;
    }
    let diagnostics = [];
    if (!args.ignoreErrors) {
        diagnostics = ts.getPreEmitDiagnostics(program);
    }
    if (diagnostics.length === 0) {
        const typeChecker = program.getTypeChecker();
        const symbols = [];
        const allSymbols = {};
        const userSymbols = {};
        const inheritingTypes = {};
        program.getSourceFiles().forEach((sourceFile, _sourceFileIdx) => {
            function inspect(node, tc) {
                if (node.kind === ts.SyntaxKind.ClassDeclaration
                    || node.kind === ts.SyntaxKind.InterfaceDeclaration
                    || node.kind === ts.SyntaxKind.EnumDeclaration
                    || node.kind === ts.SyntaxKind.TypeAliasDeclaration) {
                    const symbol = node.symbol;
                    const nodeType = tc.getTypeAtLocation(node);
                    const fullyQualifiedName = tc.getFullyQualifiedName(symbol);
                    const typeName = fullyQualifiedName.replace(/".*"\./, "");
                    const name = !args.uniqueNames ? typeName : `${typeName}.${symbol.id}`;
                    symbols.push({ name, typeName, fullyQualifiedName, symbol });
                    if (!userSymbols[name]) {
                        allSymbols[name] = nodeType;
                    }
                    if (isUserFile(sourceFile)) {
                        userSymbols[name] = symbol;
                    }
                    const baseTypes = nodeType.getBaseTypes() || [];
                    baseTypes.forEach(baseType => {
                        var baseName = tc.typeToString(baseType, undefined, ts.TypeFormatFlags.UseFullyQualifiedType);
                        if (!inheritingTypes[baseName]) {
                            inheritingTypes[baseName] = [];
                        }
                        inheritingTypes[baseName].push(name);
                    });
                }
                else {
                    ts.forEachChild(node, n => inspect(n, tc));
                }
            }
            inspect(sourceFile, typeChecker);
        });
        return new JsonSchemaGenerator(symbols, allSymbols, userSymbols, inheritingTypes, typeChecker, args);
    }
    else {
        diagnostics.forEach((diagnostic) => {
            const message = ts.flattenDiagnosticMessageText(diagnostic.messageText, "\n");
            if (diagnostic.file) {
                const { line, character } = diagnostic.file.getLineAndCharacterOfPosition(diagnostic.start);
                console.error(`${diagnostic.file.fileName} (${line + 1},${character + 1}): ${message}`);
            }
            else {
                console.error(message);
            }
        });
        return null;
    }
}
exports.buildGenerator = buildGenerator;
function generateSchema(program, fullTypeName, args = {}, onlyIncludeFiles) {
    const generator = buildGenerator(program, args, onlyIncludeFiles);
    if (generator === null) {
        return null;
    }
    if (fullTypeName === "*") {
        return generator.getSchemaForSymbols(generator.getMainFileSymbols(program, onlyIncludeFiles));
    }
    else {
        return generator.getSchemaForSymbol(fullTypeName);
    }
}
exports.generateSchema = generateSchema;
function programFromConfig(configFileName, onlyIncludeFiles) {
    const result = ts.parseConfigFileTextToJson(configFileName, ts.sys.readFile(configFileName));
    const configObject = result.config;
    const configParseResult = ts.parseJsonConfigFileContent(configObject, ts.sys, path.dirname(configFileName), {}, path.basename(configFileName));
    const options = configParseResult.options;
    options.noEmit = true;
    delete options.out;
    delete options.outDir;
    delete options.outFile;
    delete options.declaration;
    const program = ts.createProgram(onlyIncludeFiles || configParseResult.fileNames, options);
    return program;
}
exports.programFromConfig = programFromConfig;
function normalizeFileName(fn) {
    while (fn.substr(0, 2) === "./") {
        fn = fn.substr(2);
    }
    return fn;
}
function exec(filePattern, fullTypeName, args = getDefaultArgs()) {
    let program;
    let onlyIncludeFiles = undefined;
    if (REGEX_TSCONFIG_NAME.test(path.basename(filePattern))) {
        if (args.include && args.include.length > 0) {
            const globs = args.include.map(f => glob.sync(f));
            onlyIncludeFiles = [].concat(...globs).map(normalizeFileName);
        }
        program = programFromConfig(filePattern, onlyIncludeFiles);
    }
    else {
        onlyIncludeFiles = glob.sync(filePattern);
        program = getProgramFromFiles(onlyIncludeFiles, {
            strictNullChecks: args.strictNullChecks
        });
        onlyIncludeFiles = onlyIncludeFiles.map(normalizeFileName);
    }
    const definition = generateSchema(program, fullTypeName, args, onlyIncludeFiles);
    if (definition === null) {
        return;
    }
    const json = stringify(definition, { space: 4 }) + "\n\n";
    if (args.out) {
        require("fs").writeFile(args.out, json, function (err) {
            if (err) {
                console.error("Unable to write output file: " + err.message);
            }
        });
    }
    else {
        process.stdout.write(json);
    }
}
exports.exec = exec;
//# sourceMappingURL=typescript-json-schema.js.map