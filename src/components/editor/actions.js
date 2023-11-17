// Toolbar icons
import FormatQuoteIcon from "@mui/icons-material/FormatQuote";
import FormatListBulletedIcon from "@mui/icons-material/FormatListBulleted";
import FormatListNumberedIcon from "@mui/icons-material/FormatListNumbered";
import FormatIndentIncreaseIcon from "@mui/icons-material/FormatIndentIncrease";
import FormatIndentDecreaseIcon from "@mui/icons-material/FormatIndentDecrease";
import CodeIcon from "@mui/icons-material/Code";
import LooksOneIcon from "@mui/icons-material/LooksOne";
import LooksTwoIcon from "@mui/icons-material/LooksTwo";
import Looks3Icon from "@mui/icons-material/Looks3";
import HorizontalRuleIcon from "@mui/icons-material/HorizontalRule";
import ImageIcon from "@mui/icons-material/Image";
import TaskIcon from "@mui/icons-material/Task";
import LinkIcon from "@mui/icons-material/Link";
import StrikethroughSIcon from "@mui/icons-material/StrikethroughS";
import SuperscriptIcon from "@mui/icons-material/Superscript";
import SubscriptIcon from "@mui/icons-material/Subscript";
import FormatUnderlinedIcon from "@mui/icons-material/FormatUnderlined";
import FormatItalicIcon from "@mui/icons-material/FormatItalic";
import FormatBoldIcon from "@mui/icons-material/FormatBold";
import FormatColorFillIcon from "@mui/icons-material/FormatColorFill";
import FormatAlignLeftIcon from "@mui/icons-material/FormatAlignLeft";
import FormatAlignRightIcon from "@mui/icons-material/FormatAlignRight";
import FormatAlignCenterIcon from "@mui/icons-material/FormatAlignCenter";
import FormatColorTextIcon from "@mui/icons-material/FormatColorText";
import FormatColorResetIcon from "@mui/icons-material/FormatColorReset";
import DataObjectIcon from "@mui/icons-material/DataObject";
import YouTubeIcon from "@mui/icons-material/YouTube";

const getActions = (editor) => {
  return {
    sep: { sep: true },

    toggleQuoteBlock: {
      label: "toggle quote",
      icon: FormatQuoteIcon,
      action: () => editor.chain().focus().toggleBlockquote().run(),
      valid: () => editor.can().toggleBlockquote(),
      active: () => editor.isActive("blockquote"),
    },

    toggleBulletList: {
      label: "toggle bullets",
      icon: FormatListBulletedIcon,
      action: () => editor.chain().focus().toggleBulletList().run(),
      valid: () => editor.can().toggleBulletList(),
      active: () => editor.isActive("bulletList"),
    },

    toggleOrderedList: {
      label: "toggle numbers",
      icon: FormatListNumberedIcon,
      action: () => editor.chain().focus().toggleOrderedList().run(),
      valid: () => editor.can().toggleOrderedList(),
      active: () => editor.isActive("orderedList"),
    },

    increaseListLevel: {
      label: "increase bullet level",
      icon: FormatIndentIncreaseIcon,
      action: () => editor.chain().focus().sinkListItem("listItem").run(),
      valid: () => editor.can().sinkListItem("listItem"),
    },

    decreaseListLevel: {
      label: "decrease bullet level",
      icon: FormatIndentDecreaseIcon,
      action: () => editor.chain().focus().liftListItem("listItem").run(),
      valid: () => editor.can().liftListItem("listItem"),
    },

    toggleCodeBlock: {
      label: "toggle code block",
      icon: CodeIcon,
      action: () => editor.chain().focus().toggleCodeBlock().run(),
      valid: () => editor.can().toggleCodeBlock(),
      active: () => editor.isActive("codeBlock"),
    },

    toggleHeading1: {
      label: "toggle heading 1",
      icon: LooksOneIcon,
      action: () => editor.chain().focus().toggleHeading({ level: 1 }).run(),
      valid: () => editor.can().toggleHeading({ level: 1 }),
      active: () => editor.isActive("heading", { level: 1 }),
    },

    toggleHeading2: {
      label: "toggle heading 2",
      icon: LooksTwoIcon,
      action: () => editor.chain().focus().toggleHeading({ level: 2 }).run(),
      valid: () => editor.can().toggleHeading({ level: 2 }),
      active: () => editor.isActive("heading", { level: 2 }),
    },

    toggleHeading3: {
      label: "toggle heading 3",
      icon: Looks3Icon,
      action: () => editor.chain().focus().toggleHeading({ level: 3 }).run(),
      valid: () => editor.can().toggleHeading({ level: 3 }),
      active: () => editor.isActive("heading", { level: 3 }),
    },

    insertHorizontalRule: {
      label: "horizontal rule",
      icon: HorizontalRuleIcon,
      action: () =>
        editor.chain().focus().setHorizontalRule().createParagraphNear().run(),
      valid: () =>
        editor.can().chain().setHorizontalRule().createParagraphNear().run(),
    },

    insertImage: {
      label: "add image",
      icon: ImageIcon,
      action: () => {
        const url = window.prompt("Enter url for image: ");
        if (!url) return;
        editor
          .chain()
          .focus()
          .setImage({ src: url })
          .createParagraphNear()
          .run();
      },
      valid: () => editor.can().setImage(),
    },

    toggleTaskList: {
      label: "add task list",
      icon: TaskIcon,
      action: () => editor.chain().focus().toggleTaskList().run(),
      valid: () => editor.can().toggleTaskList(),
      active: () => editor.isActive("taskList"),
    },

    insertLink: {
      label: "link",
      icon: LinkIcon,
      action: () => {
        if (editor.isActive("link")) {
          editor.chain().focus().unsetLink().run();
          return;
        }

        const url = window.prompt("Enter URL: ");
        if (!url) return;

        editor.chain().focus().setLink({ href: url }).run();
      },
      active: () => editor.isActive("link"),
    },

    toggleStrikethrough: {
      label: "toggle strikethrough",
      icon: StrikethroughSIcon,
      action: () => editor.chain().focus().toggleStrike().run(),
      valid: () => editor.can().toggleStrike(),
      active: () => editor.isActive("strike"),
    },

    toggleSuperscript: {
      label: "toggle superscript",
      icon: SuperscriptIcon,
      action: () => editor.chain().focus().toggleSuperscript().run(),
      valid: () => editor.can().toggleSuperscript(),
      active: () => editor.isActive("superscript"),
    },

    toggleSubscript: {
      label: "toggle subscript",
      icon: SubscriptIcon,
      action: () => editor.chain().focus().toggleSubscript().run(),
      valid: () => editor.can().toggleSubscript(),
      active: () => editor.isActive("subscript"),
    },

    toggleUnderline: {
      label: "toggle underline",
      icon: FormatUnderlinedIcon,
      action: () => editor.chain().focus().toggleUnderline().run(),
      valid: () => editor.can().toggleUnderline(),
      active: () => editor.isActive("underline"),
    },

    toggleItalic: {
      label: "toggle italics",
      icon: FormatItalicIcon,
      action: () => editor.chain().focus().toggleItalic().run(),
      valid: () => editor.can().toggleItalic(),
      active: () => editor.isActive("italic"),
    },

    toggleBold: {
      label: "toggle bold",
      icon: FormatBoldIcon,
      action: () => editor.chain().focus().toggleBold().run(),
      valid: () => editor.can().toggleBold(),
      active: () => editor.isActive("bold"),
    },

    toggleInlineCode: {
      label: "toggle code",
      icon: CodeIcon,
      action: () => editor.chain().focus().toggleCode().run(),
      valid: () => editor.can().toggleCode(),
      active: () => editor.isActive("code"),
    },

    toggleHighlight: {
      label: "toggle highlight",
      icon: FormatColorFillIcon,
      action: () => editor.chain().focus().toggleHighlight().run(),
      valid: () => editor.can().toggleHighlight(),
      active: () => editor.isActive("highlight"),
    },

    alignLeft: {
      label: "align left",
      icon: FormatAlignLeftIcon,
      action: () => {
        if (editor.isActive({ textAlign: "left" })) {
          editor.chain().focus().unsetTextAlign().run();
          return;
        }
        editor.chain().focus().setTextAlign("left").run();
      },
      valid: () => editor.can().setTextAlign("left"),
      active: () => editor.isActive({ textAlign: "left" }),
    },

    alignRight: {
      label: "align right",
      icon: FormatAlignRightIcon,
      action: () => {
        if (editor.isActive({ textAlign: "right" })) {
          editor.chain().focus().unsetTextAlign().run();
          return;
        }
        editor.chain().focus().setTextAlign("right").run();
      },
      valid: () => editor.can().setTextAlign("right"),
      active: () => editor.isActive({ textAlign: "right" }),
    },

    alignCenter: {
      label: "align center",
      icon: FormatAlignCenterIcon,
      action: () => {
        if (editor.isActive({ textAlign: "center" })) {
          editor.chain().focus().unsetTextAlign().run();
          return;
        }
        editor.chain().focus().setTextAlign("center").run();
      },
      valid: () => editor.can().setTextAlign("center"),
      active: () => editor.isActive({ textAlign: "center" }),
    },

    setColor: {
      label: "set color",
      icon: FormatColorTextIcon,
      action: () => {
        const color = window.prompt("Enter color name or use any CSS format: ");
        if (!color) return;

        if (editor.isActive("textStyle", { color })) {
          editor.chain().focus().unsetColor();
          return;
        }

        editor.chain().focus().setColor(color).run();
      },
      valid: () => editor.can().setColor(),
    },

    unsetColor: {
      label: "clear colors",
      icon: FormatColorResetIcon,
      action: () => {
        editor.chain().focus().unsetColor().run();
      },
      valid: () => editor.can().unsetColor(),
    },

    insertEmbed: {
      label: "insert embed",
      icon: DataObjectIcon,
      action: () => {
        const url = window.prompt("URL");

        if (url) {
          editor
            .chain()
            .focus()
            .setIframe({ src: url })
            .createParagraphNear()
            .run();
        }
      },
      valid: () => editor.can().setIframe(),
    },

    insertYoutube: {
      label: "insert youtube video from link",
      icon: YouTubeIcon,
      action: () => {
        const url = window.prompt("Youtube URL");
        const extract = (url) => {
          const regExp =
            /^.*((youtu.be\/)|(v\/)|(\/u\/\w\/)|(embed\/)|(watch\?))\??v?=?([^#&?]*).*/;
          const match = url.match(regExp);
          return match && match[7].length == 11 ? match[7] : false;
        };
        if (url && extract(url)) {
          const id = extract(url);
          editor
            .chain()
            .focus()
            .setIframe({ src: `https://www.youtube.com/embed/${id}` })
            .createParagraphNear()
            .run();
        }
      },
      valid: () => editor.can().setIframe(),
    },
  };
};

export default getActions;
