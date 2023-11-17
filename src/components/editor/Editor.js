import React from "react";
import { useEditor, EditorContent } from "@tiptap/react";
import { useEffect } from "react";
import StarterKit from "@tiptap/starter-kit";
import Image from "@tiptap/extension-image";
import TaskList from "@tiptap/extension-task-list";
import TaskItem from "@tiptap/extension-task-item";
import CodeBlockLowlight from "@tiptap/extension-code-block-lowlight";
import { lowlight } from "lowlight";
import Link from "@tiptap/extension-link";
import Subscript from "@tiptap/extension-subscript";
import Superscript from "@tiptap/extension-superscript";
import Underline from "@tiptap/extension-underline";
import TextStyle from "@tiptap/extension-text-style";
import FontFamily from "@tiptap/extension-font-family";
import Color from "@tiptap/extension-color";
import Highlight from "@tiptap/extension-highlight";
import TextAlign from "@tiptap/extension-text-align";
import IFrameExtension from "./IFrameExtension";
import Code from "@tiptap/extension-code";

// Custom styles for editor
import "./Editor.css";
import "./lowlight.css";
import EditorToolbar from "./EditorToolbar";

const Editor = ({ initialContent, value, onChange }) => {
  const editor = useEditor({
    extensions: [
      StarterKit.configure({
        codeBlock: false,
        heading: {
          levels: [1, 2, 3],
        },
      }),
      Image.configure({ inline: true }),
      TaskList,
      TaskItem,
      CodeBlockLowlight.configure({
        lowlight,
        HTMLAttributes: { class: "hljs" },
      }),
      Link.configure({
        openOnClick: false,
      }),
      Subscript,
      Superscript,
      Underline,
      TextStyle,
      Highlight,
      FontFamily,
      Color,
      TextAlign.configure({
        types: ["heading", "paragraph", "image"],
      }),
      Code.configure({ HTMLAttributes: { class: "hljs" } }),
      IFrameExtension,
    ],
    onBlur({ editor }) {
      if (onChange) onChange(editor.getJSON());
    },
    content: initialContent || "",
    autofocus: false,
  });

  useEffect(() => {
    if (editor) editor.chain().clearContent().insertContent(value).blur().run();
  }, [editor, value]);

  return (
    <div className="editor-div">
      {editor && <EditorToolbar editor={editor} />}
      <EditorContent editor={editor} className="editor-wrapper" />
    </div>
  );
};

export default Editor;
