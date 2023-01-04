import {flatMap, memoize, omit, forEach} from 'lodash'
import {DEFAULT_OPTIONS, Options} from './index'
import {
  AST,
  ASTWithStandaloneName,
  hasComment,
  hasStandaloneName,
  T_ANY,
  TArray,
  TEnum,
  TInterface,
  TIntersection,
  TNamedInterface,
  TUnion,
  T_UNKNOWN
} from './types/AST'
import {log, toSafeString} from './utils'

export function generate(ast: AST, options = DEFAULT_OPTIONS): string {
  const named = declareNamedTypes(ast, options, ast.standaloneName!)
  const interfaces = declareNamedInterfaces(ast, options, ast.standaloneName!)
  const enums = declareEnums(ast, options)

  // @TODO: group by module
  const imports = generateImports(
    flatMap([
      ...flatMap(named, n => n?.imports ?? []),
      ...flatMap(interfaces, i => i?.imports ?? []),
      enums.imports ?? []
    ])
  )

  return (
    [
      options.bannerComment,
      imports,
      named
        .map(n => n?.type)
        .filter(Boolean)
        .join('\n\n'),
      interfaces
        .map(n => n?.type)
        .filter(Boolean)
        .join('\n\n'),
      enums.type
    ]
      .filter(Boolean)
      .join('\n\n') + '\n'
  ) // trailing newline
}


function generateImports(imported: TypeImport[]): string[] {
  let typeImports: {[key: string]: string[]} = {}
  let valueImports: {[key: string]: string[]} = {}

  imported.forEach(t => {
    let name = t.name
    if (t.defaultExport) {
      name = `default as {t.name}`
    }

    if (t.typeOnly) {
      typeImports[t.module] = [ ...(typeImports[t.module] ?? []), name ]
    } else {
      valueImports[t.module] = [ ...(valueImports[t.module] ?? []), name ]
    }
  })

  let importStmts: string[] = []

  forEach(typeImports, (names, module) => {
    importStmts.push(`import type {${names.join(", ")}} from "${module}"`)
  })

  forEach(valueImports, (names, module) => {
    importStmts.push(`import {${names.join(", ")}} from "${module}"`)
  })

  return importStmts
}

interface TypeImport {
  module: string
  name: string
  defaultExport?: boolean
  typeOnly?: boolean
}

function declareEnums(ast: AST, options: Options, processed = new Set<AST>()): {type: string; imports?: TypeImport[]} {
  if (processed.has(ast)) {
    return {type: ''}
  }

  processed.add(ast)

  switch (ast.type) {
    case 'ENUM':
      return generateStandaloneEnum(ast, options)
    case 'ARRAY':
      return declareEnums(ast.params, options, processed)
    case 'UNION':
    case 'INTERSECTION':
      return (() => {
        const types = ast.params.map(ast => declareEnums(ast, options, processed))
        const names = types.reduce((prev, {type}) => prev + type, '')
        return {
          imports: flatMap(types.map(t => t.imports ?? [])),
          type: names
        }
      })()
    case 'TUPLE':
      return (() => {
        const types = ast.params.map(ast => declareEnums(ast, options, processed))
        if (ast.spreadParam) {
          types.push(declareEnums(ast.spreadParam, options, processed))
        }
        const name = types.reduce((prev, {type}) => prev + type, '')

        return {
          imports: flatMap(types.map(t => t.imports ?? [])),
          type: name
        }
      })()
    case 'INTERFACE':
      return (() => {
        const types = getSuperTypesAndParams(ast).map(ast => declareEnums(ast, options, processed))
        const name = types.reduce((prev, {type}) => prev + type, '')

        return {
          imports: flatMap(types.map(t => t.imports ?? [])),
          type: name
        }
      })()
    default:
      return {type: ''}
  }
}

function declareNamedInterfaces(
  ast: AST,
  options: Options,
  rootASTName: string,
  processed = new Set<AST>()
): ({type: string; imports?: TypeImport[]} | undefined)[] {
  if (processed.has(ast)) {
    return [{type: ''}]
  }

  processed.add(ast)

  switch (ast.type) {
    case 'ARRAY':
      return declareNamedInterfaces((ast as TArray).params, options, rootASTName, processed)
    case 'INTERFACE':
      return flatMap([
        hasStandaloneName(ast) && (ast.standaloneName === rootASTName || options.declareExternallyReferenced)
          ? [generateStandaloneInterface(ast, options)]
          : [],
        ...getSuperTypesAndParams(ast).map(ast => declareNamedInterfaces(ast, options, rootASTName, processed))
      ])
    case 'INTERSECTION':
    case 'TUPLE':
    case 'UNION':
      const types = flatMap(ast.params, _ => declareNamedInterfaces(_, options, rootASTName, processed))
      if (ast.type === 'TUPLE' && ast.spreadParam) {
        types.push(...declareNamedInterfaces(ast.spreadParam, options, rootASTName, processed))
      }
      return types
  }

  return [{type: ''}]
}

function declareNamedTypes(
  ast: AST,
  options: Options,
  rootASTName: string,
  processed = new Set<AST>()
): ({type: string; imports?: TypeImport[]} | undefined)[] {
  if (processed.has(ast)) {
    return [{type: ''}]
  }

  processed.add(ast)

  switch (ast.type) {
    case 'ARRAY':
      return [
        ...declareNamedTypes(ast.params, options, rootASTName, processed),
        hasStandaloneName(ast) ? generateStandaloneType(ast, options) : undefined
      ]
    case 'ENUM':
      return [{type: ''}]
    case 'INTERFACE':
      return flatMap(getSuperTypesAndParams(ast), ast =>
        ast.standaloneName === rootASTName || options.declareExternallyReferenced
          ? declareNamedTypes(ast, options, rootASTName, processed)
          : []
      )
    case 'INTERSECTION':
    case 'TUPLE':
    case 'UNION':
      return [
        hasStandaloneName(ast) ? generateStandaloneType(ast, options) : undefined,
        ...flatMap(ast.params, ast => declareNamedTypes(ast, options, rootASTName, processed)),
        ...('spreadParam' in ast && ast.spreadParam
          ? declareNamedTypes(ast.spreadParam, options, rootASTName, processed)
          : [])
      ]
    default:
      if (hasStandaloneName(ast)) {
        return [generateStandaloneType(ast, options)]
      }
      return [{type: ''}]
  }
}

function generateTypeUnmemoized(ast: AST, options: Options): {type: string; imports?: TypeImport[]} {
  const type = generateRawType(ast, options)

  if (options.strictIndexSignatures && ast.keyName === '[k: string]') {
    return {type: `${type.type} | undefined`, imports: type.imports}
  }

  return type
}
export const generateType = memoize(generateTypeUnmemoized)

function generateRawType(ast: AST, options: Options): {type: string; imports?: TypeImport[]} {
  log('magenta', 'generator', ast)

  if (hasStandaloneName(ast)) {
    return {type: toSafeString(ast.standaloneName)}
  }

  switch (ast.type) {
    case 'ANY':
      return {type: 'any'}
    case 'ARRAY':
      return (() => {
        const {type, imports} = generateType(ast.params, options)
        return {type: type.endsWith('"') ? '(' + type + ')[]' : type + '[]', imports}
      })()

    case 'BOOLEAN':
      return {type: 'boolean'}
    case 'INTERFACE':
      return generateInterface(ast, options)
    case 'INTERSECTION':
      return generateSetOperation(ast, options)
    case 'LITERAL':
      return {type: JSON.stringify(ast.params)}
    case 'NEVER':
      return {type: 'never'}
    case 'NUMBER':
      return {type: 'number'}
    case 'NULL':
      return {type: 'null'}
    case 'OBJECT':
      return {type: 'object'}
    case 'REFERENCE':
      return {type: ast.params}
    case 'STRING':
      return {type: 'string'}
    case 'TUPLE':
      return (() => {
        const minItems = ast.minItems
        const maxItems = ast.maxItems || -1

        let spreadParam = ast.spreadParam
        const astParams = [...ast.params]
        if (minItems > 0 && minItems > astParams.length && ast.spreadParam === undefined) {
          // this is a valid state, and JSONSchema doesn't care about the item type
          if (maxItems < 0) {
            // no max items and no spread param, so just spread any
            spreadParam = options.unknownAny ? T_UNKNOWN : T_ANY
          }
        }
        if (maxItems > astParams.length && ast.spreadParam === undefined) {
          // this is a valid state, and JSONSchema doesn't care about the item type
          // fill the tuple with any elements
          for (let i = astParams.length; i < maxItems; i += 1) {
            astParams.push(options.unknownAny ? T_UNKNOWN : T_ANY)
          }
        }

        function addSpreadParam(params: string[]): string[] {
          if (spreadParam) {
            const spread = '...(' + generateType(spreadParam, options).type + ')[]'
            params.push(spread)
          }
          return params
        }

        function paramsToString(params: string[]): string {
          return '[' + params.join(', ') + ']'
        }

        const paramsList = astParams.map(param => generateType(param, options))
        const imports = flatMap(paramsList.map(p => p.imports ?? []))

        if (paramsList.length > minItems) {
          /*
if there are more items than the min, we return a union of tuples instead of
using the optional element operator. This is done because it is more typesafe.

// optional element operator
type A = [string, string?, string?]
const a: A = ['a', undefined, 'c'] // no error

// union of tuples
type B = [string] | [string, string] | [string, string, string]
const b: B = ['a', undefined, 'c'] // TS error
*/

          const cumulativeParamsList: string[] = paramsList.map(p => p.type).slice(0, minItems)
          const typesToUnion: string[] = []

          if (cumulativeParamsList.length > 0) {
            // actually has minItems, so add the initial state
            typesToUnion.push(paramsToString(cumulativeParamsList))
          } else {
            // no minItems means it's acceptable to have an empty tuple type
            typesToUnion.push(paramsToString([]))
          }

          for (let i = minItems; i < paramsList.length; i += 1) {
            cumulativeParamsList.push(paramsList[i].type)

            if (i === paramsList.length - 1) {
              // only the last item in the union should have the spread parameter
              addSpreadParam(cumulativeParamsList)
            }

            typesToUnion.push(paramsToString(cumulativeParamsList))
          }

          return {type: typesToUnion.join('|'), imports}
        }

        // no max items so only need to return one type
        return {
          type: paramsToString(addSpreadParam(paramsList.map(p => p.type))),
          imports
        }
      })()
    case 'UNION':
      return generateSetOperation(ast, options)
    case 'UNKNOWN':
      return {type: 'unknown'}
    case 'CUSTOM_TYPE':
      if (ast.params.module) {
        return {
          type: ast.params.name,
          imports: [{module: ast.params.module!, name: ast.params.name, defaultExport: ast.params.defaultExport}]
        }
      }
      return {type: ast.params.name}
  }
}

/**
 * Generate a Union or Intersection
 */
function generateSetOperation(ast: TIntersection | TUnion, options: Options): {type: string; imports?: TypeImport[]} {
  const members = (ast as TUnion).params.map(_ => generateType(_, options))
  const separator = ast.type === 'UNION' ? '|' : '&'

  return members.length === 1
    ? members[0]
    : {
        type: '(' + members.map(m => m.type).join(' ' + separator + ' ') + ')',
        imports: flatMap(members.map(m => m.imports ?? []))
      }
}

function generateInterface(ast: TInterface, options: Options): {type: string; imports?: TypeImport[]} {
  const fields = ast.params
    .filter(_ => !_.isPatternProperty && !_.isUnreachableDefinition)
    .map(
      ({isRequired, keyName, ast}) =>
        [isRequired, keyName, ast, generateType(ast, options)] as [
          boolean,
          string,
          AST,
          ReturnType<typeof generateType>
        ]
    )

  return {
    imports: flatMap(fields, ([_1, _2, _3, {imports}]) => imports ?? []),
    type:
      `{` +
      '\n' +
      fields
        .map(
          ([isRequired, keyName, ast, {type}]) =>
            (hasComment(ast) && !ast.standaloneName ? generateComment(ast.comment) + '\n' : '') +
            escapeKeyName(keyName) +
            (isRequired ? '' : '?') +
            ': ' +
            (hasStandaloneName(ast) ? toSafeString(type) : type)
        )
        .join('\n') +
      '\n' +
      '}'
  }
}

function generateComment(comment: string): string {
  return ['/**', ...comment.split('\n').map(_ => ' * ' + _), ' */'].join('\n')
}

function generateStandaloneEnum(ast: TEnum, options: Options): {type: string; imports?: TypeImport[]} {
  const types = ast.params.map(({ast, keyName}) => ({keyName, ...generateType(ast, options)}))
  const names = types.map(t => t.keyName + ' = ' + t.type)
  const imports = flatMap(types, ({imports}) => imports ?? [])

  return {
    imports,
    type:
      (hasComment(ast) ? generateComment(ast.comment) + '\n' : '') +
      'export ' +
      (options.enableConstEnums ? 'const ' : '') +
      `enum ${toSafeString(ast.standaloneName)} {` +
      '\n' +
      names.join(',\n') +
      '\n' +
      '}'
  }
}

function generateStandaloneInterface(ast: TNamedInterface, options: Options): {type: string; imports?: TypeImport[]} {
  const iface = generateInterface(ast, options)
  return {
    imports: iface.imports,
    type:
      (hasComment(ast) ? generateComment(ast.comment) + '\n' : '') +
      `export interface ${toSafeString(ast.standaloneName)} ` +
      (ast.superTypes.length > 0
        ? `extends ${ast.superTypes.map(superType => toSafeString(superType.standaloneName)).join(', ')} `
        : '') +
      iface.type
  }
}

function generateStandaloneType(ast: ASTWithStandaloneName, options: Options): {type: string; imports?: TypeImport[]} {
  const {type, imports} = generateType(omit<AST>(ast, 'standaloneName') as AST /* TODO */, options)

  const exportedType =
    (hasComment(ast) ? generateComment(ast.comment) + '\n' : '') +
    `export type ${toSafeString(ast.standaloneName)} = ${type}`

  return {
    imports,
    type: type ? exportedType : ''
  }
}

function escapeKeyName(keyName: string): string {
  if (keyName.length && /[A-Za-z_$]/.test(keyName.charAt(0)) && /^[\w$]+$/.test(keyName)) {
    return keyName
  }
  if (keyName === '[k: string]') {
    return keyName
  }
  return JSON.stringify(keyName)
}

function getSuperTypesAndParams(ast: TInterface): AST[] {
  return ast.params.map(param => param.ast).concat(ast.superTypes)
}
