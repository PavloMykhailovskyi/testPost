import { babel } from '@rollup/plugin-babel';
import resolve from '@rollup/plugin-node-resolve';
import external from 'rollup-plugin-peer-deps-external';
import postcss from 'rollup-plugin-postcss';
import commonjs from '@rollup/plugin-commonjs';
import json from '@rollup/plugin-json';

export default [
  {
    input: './src/index.js',
    output: [
      {
        file: 'dist/index.js',
        format: 'cjs',
        
      },
      {
        file: 'dist/index.es.js',
        format: 'es',
        exports: 'named',
      }
    ],
    external: [ /@babel\/runtime/,'react','react-dom','@mui/material','@emotion/react','@emotion/styled','@mui/icons-material','axios','@tiptap/core','@tiptap/react','@tiptap/starter-kit','@tiptap/extension-code','@tiptap/extension-code-block-lowlight','@tiptap/extension-color','@tiptap/extension-font-family','@tiptap/extension-highlight','@tiptap/extension-image','@tiptap/extension-link','@tiptap/extension-subscript','@tiptap/extension-superscript','@tiptap/extension-table','@tiptap/extension-table-cell','@tiptap/extension-table-header','@tiptap/extension-table-row','@tiptap/extension-task-item','@tiptap/extension-task-list','@tiptap/extension-text-align','@tiptap/extension-text-style','@tiptap/extension-underline','lowlight'],
    plugins: [
  
      postcss({
        plugins: [],
        minimize: true,
      }),
      babel({
        exclude: 'node_modules/**',
        presets: ['@babel/preset-react'],
        plugins: ['@babel/transform-runtime'],
        babelHelpers:'runtime'
      }),
      external(),
      json(),
      resolve({preferBuiltins:true,browser: true}),
      commonjs()
    ]
  }
];
