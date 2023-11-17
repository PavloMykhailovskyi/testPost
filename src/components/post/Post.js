import React from "react";
import {
  Card,
  CardContent,
  Box,
  Divider,
  Typography,
  Chip,
  CardHeader,
  Avatar
} from "@mui/material";
import Likes from "./Likes";
import Viewer from "./Viewer";
import CommentList from "../commentlist/CommentList";

const Post = ({
  postID,
  title,
  subtitle,
  author,
  authorpic,
  date,
  content,
  likes,
  tags,
}) => {

  const current = new Date(date);
 const monthname = [{ n: 0, name: "January" }, { n: 1, name: "Feburary" }, { n: 2, name: "March" }, { n: 3, name: "April" }, { n: 4, name: "May" }, { n: 5, name: "June" }, { n: 6, name: "July" }, { n: 7, name: "August" }, { n: 8, name: "September" }, { n: 9, name: "October" }, { n: 10, name: "November" }, { n: 11, name: "December" }].find((v) => {
    if (current.getMonth() == v.n) {
      return v
    }

  })

   const d = `${current.getDate()} ${monthname.name} ${current.getFullYear()}`;
  return (
    <Card sx={{  marginTop:7}} variant="outlined">
      <CardContent
        sx={{
          display: "flex",
          flexDirection: "column",
          gap: 2,
          alignItems: "center",
        
        }}
      >
        <Box
          sx={{
            display: "flex",
            flexDirection: "column",
            gap: 2,
            alignItems: "center",
            my: 4,
          }}
        >
          <Typography variant="h3">{title}</Typography>
          <Typography variant="body" sx={{ fontStyle: "italic" }}>
            {subtitle}
          </Typography>
         <Likes postid={postID} count={likes}  />
        </Box>
        <Divider sx={{ width: "100%" }} />
        <Box sx={{ width: "100%", px: 4 }}>
          <Viewer content={content} />
        </Box>
        <Divider sx={{ width: "100%" }} />
        <Box >
                {tags.length!=0 && tags.map((e)=>(
               <Chip sx={{color:"blue",borderColor:"blue",margin:0.5}} label={e} variant="outlined"/>
                ))}
        </Box>
        
          <Card variant="outlined">
            <CardHeader
            title={<span style={{fontSize:"0.85em"}}>{`By ${author}`}</span>}
            subheader={<span style={{fontSize:"0.75em"}}>{`Published - ${d}`}</span>}
            avatar={<Avatar src={authorpic}></Avatar>}
            />
              
            
          </Card>
        
        <Divider sx={{ width: "100%" }} />
        <Typography variant="h6" align="center">
          Comments
        </Typography>
        <CommentList postID={postID} />
      </CardContent>
    </Card>
  );
};

export default Post;
