import React from "react";
import {
  Box,
  Button,
  TextField,
  Avatar,
  Card,
  CardHeader,
  CardContent,
  Chip,
  Stack,
} from "@mui/material";
import { useState,useRef,useEffect,useContext } from "react";
import Editor from "./Editor";
import useMediaQuery from "@mui/material/useMediaQuery";
import EditIcon from '@mui/icons-material/Edit';
import axios from "axios";
import { BlogContext } from "../context/blog-context";


import "./Createpost.css";
export const CreatePost = ({authorID}) => {
  const ctx=useContext(BlogContext)
 
  const matches = useMediaQuery("(max-width:600px)");
  const [title, setTitle] = useState("");
  const [authorName, setAuthorName] = useState("");
  const [thumbnil, setThumbnil] = useState("https://www.garyvaynerchuk.com/wp-content/uploads/150624-The_Current_state_of_blogging_1200x628-01.png");
  const [subtitle, setSubtitle] = useState("");
  const [tags, setTags] = useState([]);
  const [postContent, setPostContent] = useState("");
  const [error, setError] = useState({title:false,subtitle:false,tag:false});
  const tagfield = useRef("");
  const thumbnilfield = useRef("");

  useEffect( () => {
    async function makeRequest(){
    try {
      const authRes = await axios.get(`http://localhost:5000/api/authors/${authorID}`,{headers:{ "Authorization": `${ctx.key} ${ctx.id}`}});
      const auth = authRes.data.name;
      setAuthorName(auth)
    } catch (error) {
      console.error(error);
    }
}
makeRequest()
  }, []);
  const handleChange=(l,v)=>{
   
    switch(l){
      case "Title":
        
          if(v==""){
            
            let o=error;
            o.title=true;
             setError(o)
          }else{
            let o=error;
            o.title=false;
             setError(o)
          }
          break;
      case "Subtitle":
        if(v==""){
          let o=error;
          o.subtitle=true;
           setError(o)
      }else{
        let o=error;
        o.subtitle=false;
         setError(o)
      }
          break;
    }
  }
  const handleSubmit = async (e) => {
    e.preventDefault();
    
    if(error.title==true || title==""){
     alert("title field is Empty")
     return
   }
   if(error.subtitle==true || subtitle==""){
    alert("subtitle field is Empty")
    return
  }
  if(postContent.length==0){
    alert("Blog content Empty")
    return
  }
    const postObject = {
      title,
      subtitle,
      content: postContent,
      auth: authorID,
      tags: tags,
      thumb:thumbnil
    };
   
    setTitle("");
    setSubtitle("");
    setThumbnil("https://www.garyvaynerchuk.com/wp-content/uploads/150624-The_Current_state_of_blogging_1200x628-01.png")
    setTags("");
    setPostContent("");
   


    try {
      const res = await axios.post(ctx.baseUrl+"api/posts/", postObject,{headers:{ "Authorization": `${ctx.key} ${ctx.id}`}});
      alert("Post Published Succesfully")
    } catch (error) {
      alert(error)
    }
  };

  const TagHandelar = () => {
    if (tagfield.current.value != "") {
      let has = "#".concat(tagfield.current.value);
      setTags([...tags, has]);
      tagfield.current.value = "";
    }
  };
  const ThumbnilHandelar = () => {
    if (thumbnilfield.current.value != "") {
    setThumbnil(thumbnilfield.current.value)
    console.log(thumbnilfield.current.value)
    }
  };

  const handleDelete = (e) => {
    setTags(tags.filter((item) => item !== e));
  };
   const current = new Date();
 const monthname = [{ n: 0, name: "January" }, { n: 1, name: "Feburary" }, { n: 2, name: "March" }, { n: 3, name: "April" }, { n: 4, name: "May" }, { n: 5, name: "June" }, { n: 6, name: "July" }, { n: 7, name: "August" }, { n: 8, name: "September" }, { n: 9, name: "October" }, { n: 10, name: "November" }, { n: 11, name: "December" }].find((v) => {
    if (current.getMonth() == v.n) {
      return v
    }

  })

  const date = `${current.getDate()} ${monthname.name} ${current.getFullYear()}`;
  return (
    <Box
      sx={{
        display: "flex",
        flexDirection: "column",
        gap: 2,
       
        border: "2px solid lightgreen",
        borderRadius: "20px",
        padding: 2,
        backgroundColor:"white"
      }}
    >
     <span style={{color:"green",borderBottom:"1px solid lightgreen"}}><EditIcon sx={{fontSize:"1em",marginRight:1}}/>{authorName} - <span style={{color:"grey",align:"right"}}>{date}</span></span>
        
        <Box
          sx={{
            display: "flex",
            flexDirection: "column",
            gap: 2,
            alignItems: "stretch",
          }}
        >
          <Box
            sx={{
              display: "flex",
              flexDirection: "row",
              gap: 2,
              alignItems: "center",
            }}
          >
            <TextField
              label="Title"
              name="lol"
              variant="outlined"
              sx={{ width: "90%" }}
              onChange={(e) => {setTitle(e.target.value);handleChange(e.target.labels[0].outerText,e.target.value)}}
              onBlur={(e) => {handleChange(e.target.labels[0].outerText,e.target.value)}}
              error={error.title}
              helperText={error.title?"Title field Empty":""}
              value={title}

           
            />
  
     
          </Box>
        
          <Box
            sx={{
              display: "flex",
              flexDirection: matches ? "column" : "row",
              gap: 2,
              alignItems: "center",
            }}
          >
           <Card
              elevation={0}
              sx={{ width: matches ? "100%" : "50%", border: "1px solid lightgreen" }}
            >
               <CardHeader
                title={
                  <Box
                    sx={{
                      display: "flex",
                      flexDirection: matches ? "column" : "row",
                      gap: 2,
                      alignItems: "center",
                    }}
                  >
                    <Avatar key={thumbnil} sx={{width:matches?"30%":"15%",marginTop:1}} variant="rounded" src={thumbnil}>

                    </Avatar>
                    <TextField
                      sx={{ width: matches ? "100%" : "70%" }}
                      label="Change Thumbnail Link"
                      variant="outlined"
                      inputRef={thumbnilfield}
                    />
                    <Button
                      variant="outlined"
                      color="success"
                      
                      onClick={ThumbnilHandelar}
                    >
                      Change
                    </Button>
                  </Box>
                }
              ></CardHeader>
            </Card>
            <Card
              elevation={0}
              sx={{ width: matches ? "100%" : "50%", border: "1px solid lightgreen" }}
            >
              <CardHeader
                title={
                  <Box
                    sx={{
                      display: "flex",
                      flexDirection: matches ? "column" : "row",
                      gap: 2,
                    }}
                  >
                    <TextField
                      sx={{ width: matches ? "100%" : "70%" }}
                      label="Add Tags "
                      variant="outlined"
                      inputRef={tagfield}
                      inputProps={{
                        maxLength: 30,
                      }}
                      onKeyPress={(e) => {
                        if (e.key === 'Enter') {
                          TagHandelar();
                        }
                      }}
                      InputProps={{
                        startAdornment: (
                          <span style={{color:"grey",marginRight:2,paddingRight:2}}>#</span>
                        ),
                      }}
                    />
                    <Button
                      variant="outlined"
                      color="success"
                      component="button"
                      onClick={TagHandelar}

                    >
                      Add
                    </Button>
                  </Box>
                }
              ></CardHeader>
              <CardContent className="tagCont">
                <Stack sx={{ overflowX: "scroll" }} direction="row" spacing={2}>
                  {tags.length != 0 &&
                    tags.map((e) => (
                      <Chip
                        sx={{ color: "blue", borderColor: "blue" }}
                        label={e}
                        variant="outlined"
                        onDelete={() => handleDelete(e)}
                      />
                    ))}
                </Stack>
              </CardContent>
            </Card>
          </Box>

          <TextField
            label="Subtitle"
            variant="standard"
            multiline
            rows={2}
            onChange={(e) => {setSubtitle(e.target.value);handleChange("Subtitle",e.target.value)}}
            onBlur={(e) => {handleChange("Subtitle",e.target.value)}}
            error={error.subtitle}
            helperText={error.subtitle?"SubTitle field Empty":""}
            value={subtitle}
          />
        </Box>
    

      <Editor onChange={setPostContent} value={postContent} />
      <Button
              variant="contained"
              color="success"
              component="button"
              onClick={handleSubmit}
             sx={{width:"22%",}}
             
            >
              Publish
            </Button>
    </Box>
  );
};


